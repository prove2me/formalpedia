-- Prove2me | Theorems.Thm_MixedVolFPRAS_Main_theorem_3_3
-- name    : MixedVolFPRAS.Main.theorem_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:31:52.839787+00:00
-- url     : https://prove2.me/theorems/ae069bbb-f623-4468-8069-9f229701f41a
-- title:
--   Theorem 3.3 — FPRAS for smooth R-well-rounded bodies, cost polynomial in n, 1/ε, log(1/δ), Λ/λ, R, M and the input length
-- statement:
--   There are one program $P$ of the machine model (`Machine`) and constants $C>0$, $d$ such that the following holds for every $n\ge3$. Let $K_1,\dots,K_n\subseteq\mathbb{R}^n$ be well-presented (valid weak membership oracles $O_i$, initial data $(x^{\mathrm{init}}_i,r_i,R_i)$), $R$-well-rounded and $(\lambda,\Lambda,M)$-smooth convex bodies, with rational parameters $R>0$, $\lambda,\Lambda,M$ and rational $0<\varepsilon,\delta<1$. Run $P$ on the input $[n,\varepsilon,\delta,x^{\mathrm{init}}_1,r_1,R_1,\dots,x^{\mathrm{init}}_n,r_n,R_n,R,\lambda,\Lambda,M]$ (code length $L$) with
--
--   $$B=C\big(1+n+L+\lceil1/\varepsilon\rceil+\lceil\log_2\lceil1/\delta\rceil\rceil+\lceil\Lambda/\lambda\rceil+\lceil R\rceil+\lceil M\rceil\big)^d .$$
--
--   Then on every random bit stream the run halts within $B$ steps using at most $B$ oracle calls and $B$ bit operations, and at least $(1-\delta)2^B$ of the $2^B$ bit strings of length $B$ yield an output $\hat V$ with
--
--   $$(1-\varepsilon)\,V_n(K_1,\dots,K_n)\le\hat V\le(1+\varepsilon)\,V_n(K_1,\dots,K_n).$$
--
--   This is the smooth, well-rounded special case of the main theorem, the base of the reduction (cost polynomial in $R$ itself, not its bit length).
--
--   Differences from the source:
--   - encoding: "randomized algorithm … polynomial in n, 1/ε, log(1/δ), Λ/λ, R, M and the total binary length" → one program of the `Machine` model with constants $C>0$, $d$ fixed before $n$, budget $C(\mathrm{size}+\lceil\Lambda/\lambda\rceil+\lceil R\rceil+\lceil M\rceil)^d$ on every bit stream, success counted over the $2^B$ bit strings; reason: the paper names no machine; this is the published `CommonBasesFPRAS` form.
--   - encoding: "the parameters R, λ, Λ, M, ε, δ are supplied as rational numbers" → appended to the input list after the data, in the order $R,\lambda,\Lambda,M$; reason: a fixed input layout.
--   - encoding: $R$-well-rounded (Definition 3.1, "for R > 0") → binder `0 < R`; reason: Definition 3.1 assumes it.
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), p. 13, Theorem 3.3

import Mathlib
import Definitions.Def_MixedVolFPRAS_Main_MixedVolume
import Definitions.Def_MixedVolFPRAS_Main_WeakOracle
import Definitions.Def_MixedVolFPRAS_Main_Machine
import Definitions.Def_MixedVolFPRAS_Main_Smoothness

namespace MixedVolFPRAS.Main

/-- **Theorem 3.3.** One program and constants `C > 0`, `d` such that for every `n ≥ 3`, all
well-presented, `R`-well-rounded and `(λ, Λ, M)`-smooth convex bodies `K₁, …, Kₙ` (parameters
`R, λ, Λ, M, ε, δ` rational, supplied after the data), `0 < ε, δ < 1`: with
`B = C (1 + n + L + ⌈1/ε⌉ + ⌈log₂⌈1/δ⌉⌉ + ⌈Λ/λ⌉ + ⌈R⌉ + ⌈M⌉)^d`, every run halts within `B` steps,
`B` oracle calls and `B` bit operations, and at least a `(1 − δ)` fraction of the length-`B` bit
strings give `(1 − ε) Vₙ(K) ≤ V̂ ≤ (1 + ε) Vₙ(K)`. -/
theorem theorem_3_3 :
    ∃ (k s : ℕ) (P : Program k s) (C d : ℕ), 0 < C ∧
      ∀ (n : ℕ), 3 ≤ n →
      ∀ (K : Fin n → Set (E n)) (O : MemOracle n) (xinit : Fin n → Fin n → ℚ)
        (r R0 : Fin n → ℚ) (R lam Lam M ε δ : ℚ),
        (∀ i, IsWellPresented (K i) (O i) (xinit i) (r i) (R0 i)) →
        0 < R → (∀ i, IsWellRounded (R : ℝ) (K i)) →
        (∀ i, IsSmoothBody (lam : ℝ) (Lam : ℝ) (M : ℝ) (K i)) →
        0 < ε → ε < 1 → 0 < δ → δ < 1 →
        RunsWithinBudget P O (presentationInput n ε δ xinit r R0 ++ [R, lam, Lam, M])
            (C * (sizeParam n (presentationInput n ε δ xinit r R0 ++ [R, lam, Lam, M]) ε δ +
              ⌈Lam / lam⌉₊ + ⌈R⌉₊ + ⌈M⌉₊) ^ d) ∧
          (1 - δ) * (2 : ℚ) ^ (C * (sizeParam n (presentationInput n ε δ xinit r R0 ++
              [R, lam, Lam, M]) ε δ + ⌈Lam / lam⌉₊ + ⌈R⌉₊ + ⌈M⌉₊) ^ d) ≤
            (goodCount P O (presentationInput n ε δ xinit r R0 ++ [R, lam, Lam, M])
              (C * (sizeParam n (presentationInput n ε δ xinit r R0 ++ [R, lam, Lam, M]) ε δ +
                ⌈Lam / lam⌉₊ + ⌈R⌉₊ + ⌈M⌉₊) ^ d)
              (RelApprox ε (mixedVolume K)) : ℚ) := by sorry

end MixedVolFPRAS.Main
