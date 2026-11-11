-- Prove2me | Theorems.Thm_MixedVolFPRAS_Main_theorem_1_2
-- name    : MixedVolFPRAS.Main.theorem_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:31:24.902747+00:00
-- url     : https://prove2.me/theorems/eb6fa739-0b45-4bf1-a323-32f090b75ef1
-- title:
--   Theorem 1.2 — an FPRAS for mixed volumes of n well-presented convex bodies with weak membership oracles
-- statement:
--   There are one program $P$ of the machine model (`Machine`: bit stacks, fair coins, weak-membership queries) and constants $C>0$, $d$, fixed once and for all, such that the following holds for every $n\ge1$. Let $K_1,\dots,K_n\subseteq\mathbb{R}^n$ be well-presented convex bodies: each comes with an arbitrary valid weak membership oracle $O_i$ (Definition 1.1) and rational initial data $x^{\mathrm{init}}_i\in K_i$, $0<r_i\le R_i$ with $x^{\mathrm{init}}_i+r_iB_2^n\subseteq K_i\subseteq x^{\mathrm{init}}_i+R_iB_2^n$. Let $0<\varepsilon,\delta<1$ be rational. Run $P$ with oracles $O$ on the input $[n,\varepsilon,\delta,x^{\mathrm{init}}_1,r_1,R_1,\dots,x^{\mathrm{init}}_n,r_n,R_n]$, whose code has length $L$, and set
--
--   $$B=C\big(1+n+L+\lceil1/\varepsilon\rceil+\lceil\log_2\lceil1/\delta\rceil\rceil\big)^d .$$
--
--   Then on every random bit stream the run has halted after $B$ steps, having used at most $B$ oracle calls and at most $B$ bit operations, and at least $(1-\delta)2^B$ of the $2^B$ random bit strings of length $B$ yield an output $\hat V$ with
--
--   $$(1-\varepsilon)\,V_n(K_1,\dots,K_n)\le\hat V\le(1+\varepsilon)\,V_n(K_1,\dots,K_n).$$
--
--   That is, there is a fully polynomial randomized approximation scheme for the mixed volume of convex bodies given by weak membership oracles, with cost polynomial in $n$, $1/\varepsilon$, $\log(1/\delta)$ and the binary length of the data — polylogarithmic in the aspect ratios $R_i/r_i$. It disproves Gurvits's conjecture that no efficient algorithm exists.
--
--   Differences from the source:
--   - encoding: "randomized algorithm", "number of weak membership oracle calls and bit operations" → one fixed program of the `Machine` model, its oracle-call and bit-operation counters, worst case over every random bit stream; reason: the paper names no machine model; this is the published `CommonBasesFPRAS` form.
--   - encoding: "polynomial in n, 1/ε, log(1/δ) and the total binary length of ε, δ and the data" → $C(1+n+L+\lceil1/\varepsilon\rceil+\lceil\log_2\lceil1/\delta\rceil\rceil)^d$ with $C>0$, $d$ chosen before $n$ and the input, $L$ the length of the self-delimiting code of the input list; reason: an explicit polynomial; $L$ is the binary length up to a constant factor.
--   - encoding: $\Pr[\dots]\ge1-\delta$ → $(1-\delta)2^B\le$ number of good bit strings of length $B$; reason: probability over the algorithm's fair coins, all of which are read within $B$ steps.
--   - encoding: $n\in\mathbb N$ → `1 ≤ n`; reason: there are no bodies when $n=0$.
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), p. 3, Theorem 1.2

import Mathlib
import Definitions.Def_MixedVolFPRAS_Main_MixedVolume
import Definitions.Def_MixedVolFPRAS_Main_WeakOracle
import Definitions.Def_MixedVolFPRAS_Main_Machine

namespace MixedVolFPRAS.Main

/-- **Theorem 1.2 (FPRAS for mixed volumes).** One program `P` and one pair of constants
`C > 0`, `d`, fixed before the input, such that for every `n ≥ 1`, all well-presented convex bodies
`K₁, …, Kₙ ⊆ ℝⁿ` (every valid weak membership oracle) and all rational `0 < ε, δ < 1`: with
`B = C (1 + n + L + ⌈1/ε⌉ + ⌈log₂⌈1/δ⌉⌉)^d`, every run halts within `B` steps using at most `B`
oracle calls and `B` bit operations, and at least a `(1 − δ)` fraction of the `2^B` random bit
strings of length `B` give an output `V̂` with `(1 − ε) Vₙ(K) ≤ V̂ ≤ (1 + ε) Vₙ(K)`. -/
theorem theorem_1_2 :
    ∃ (k s : ℕ) (P : Program k s) (C d : ℕ), 0 < C ∧
      ∀ (n : ℕ), 1 ≤ n →
      ∀ (K : Fin n → Set (E n)) (O : MemOracle n) (xinit : Fin n → Fin n → ℚ)
        (r R : Fin n → ℚ) (ε δ : ℚ),
        (∀ i, IsWellPresented (K i) (O i) (xinit i) (r i) (R i)) →
        0 < ε → ε < 1 → 0 < δ → δ < 1 →
        RunsWithinBudget P O (presentationInput n ε δ xinit r R)
            (C * sizeParam n (presentationInput n ε δ xinit r R) ε δ ^ d) ∧
          (1 - δ) * (2 : ℚ) ^ (C * sizeParam n (presentationInput n ε δ xinit r R) ε δ ^ d) ≤
            (goodCount P O (presentationInput n ε δ xinit r R)
              (C * sizeParam n (presentationInput n ε δ xinit r R) ε δ ^ d)
              (RelApprox ε (mixedVolume K)) : ℚ) := by sorry

end MixedVolFPRAS.Main
