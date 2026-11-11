-- Prove2me | Theorems.Thm_MixedVolFPRAS_Main_theorem_4_1
-- name    : MixedVolFPRAS.Main.theorem_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:31:44.27796+00:00
-- url     : https://prove2.me/theorems/6e1c0b5d-d797-4067-9bda-96644f470709
-- title:
--   Theorem 4.1 — FPRAS for R-well-rounded bodies, cost polynomial in n, 1/ε, log(1/δ), R and the input length
-- statement:
--   There are one program $P$ of the machine model and constants $C>0$, $d$ such that for every $n\ge3$, all well-presented $R$-well-rounded convex bodies $K_1,\dots,K_n\subseteq\mathbb{R}^n$ (any valid weak membership oracles, initial data $(x^{\mathrm{init}}_i,r_i,R_i)$), rational $R>0$ and rational $0<\varepsilon,\delta<1$: on the input $[n,\varepsilon,\delta,x^{\mathrm{init}}_1,r_1,R_1,\dots,x^{\mathrm{init}}_n,r_n,R_n,R]$ (code length $L$), with
--
--   $$B=C\big(1+n+L+\lceil1/\varepsilon\rceil+\lceil\log_2\lceil1/\delta\rceil\rceil+\lceil R\rceil\big)^d,$$
--
--   every run halts within $B$ steps using at most $B$ oracle calls and $B$ bit operations, and at least $(1-\delta)2^B$ of the bit strings of length $B$ give an output $\hat V$ with $(1-\varepsilon)V_n(K_1,\dots,K_n)\le\hat V\le(1+\varepsilon)V_n(K_1,\dots,K_n)$.
--
--   This removes the smoothness assumption of Theorem 3.3; it is Theorem 1.2 with cost polynomial in the aspect ratio $R$ rather than in its bit length.
--
--   Differences from the source:
--   - encoding: "randomized algorithm … polynomial in n, 1/ε, log(1/δ), R and the total binary length" → one program of the `Machine` model with constants $C>0$, $d$ fixed before $n$, budget $C(\mathrm{size}+\lceil R\rceil)^d$ on every bit stream, success counted over the $2^B$ bit strings; reason: the paper names no machine; this is the published `CommonBasesFPRAS` form.
--   - encoding: "the parameters R, ε, δ are supplied as rational numbers" → $R$ appended to the input list after the data; reason: a fixed input layout.
--   - encoding: $R$-well-rounded (Definition 3.1, "for R > 0") → binder `0 < R`; reason: Definition 3.1 assumes it.
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), p. 17, Theorem 4.1

import Mathlib
import Definitions.Def_MixedVolFPRAS_Main_MixedVolume
import Definitions.Def_MixedVolFPRAS_Main_WeakOracle
import Definitions.Def_MixedVolFPRAS_Main_Machine
import Definitions.Def_MixedVolFPRAS_Main_Smoothness

namespace MixedVolFPRAS.Main

/-- **Theorem 4.1.** One program and constants `C > 0`, `d` such that for every `n ≥ 3`, all
well-presented `R`-well-rounded convex bodies `K₁, …, Kₙ` (`R, ε, δ` rational, `R` supplied after
the data), `0 < ε, δ < 1`: with `B = C (1 + n + L + ⌈1/ε⌉ + ⌈log₂⌈1/δ⌉⌉ + ⌈R⌉)^d`, every run halts
within `B` steps, `B` oracle calls and `B` bit operations, and at least a `(1 − δ)` fraction of the
length-`B` bit strings give `(1 − ε) Vₙ(K) ≤ V̂ ≤ (1 + ε) Vₙ(K)`. -/
theorem theorem_4_1 :
    ∃ (k s : ℕ) (P : Program k s) (C d : ℕ), 0 < C ∧
      ∀ (n : ℕ), 3 ≤ n →
      ∀ (K : Fin n → Set (E n)) (O : MemOracle n) (xinit : Fin n → Fin n → ℚ)
        (r R0 : Fin n → ℚ) (R ε δ : ℚ),
        (∀ i, IsWellPresented (K i) (O i) (xinit i) (r i) (R0 i)) →
        0 < R → (∀ i, IsWellRounded (R : ℝ) (K i)) →
        0 < ε → ε < 1 → 0 < δ → δ < 1 →
        RunsWithinBudget P O (presentationInput n ε δ xinit r R0 ++ [R])
            (C * (sizeParam n (presentationInput n ε δ xinit r R0 ++ [R]) ε δ + ⌈R⌉₊) ^ d) ∧
          (1 - δ) * (2 : ℚ) ^ (C * (sizeParam n (presentationInput n ε δ xinit r R0 ++ [R]) ε δ +
              ⌈R⌉₊) ^ d) ≤
            (goodCount P O (presentationInput n ε δ xinit r R0 ++ [R])
              (C * (sizeParam n (presentationInput n ε δ xinit r R0 ++ [R]) ε δ + ⌈R⌉₊) ^ d)
              (RelApprox ε (mixedVolume K)) : ℚ) := by sorry

end MixedVolFPRAS.Main
