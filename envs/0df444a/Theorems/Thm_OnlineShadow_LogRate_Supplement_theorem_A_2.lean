-- Prove2me | Theorems.Thm_OnlineShadow_LogRate_Supplement_theorem_A_2
-- name    : OnlineShadow.LogRate.Supplement.theorem_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:56:31.773672+00:00
-- url     : https://prove2.me/theorems/5089e26c-b822-428d-bc3e-43804ada0716
-- title:
--   Theorem A.2 — Best Observable Selection with expected regret $\le\sqrt{\ln m/2n}$
-- statement:
--   In the (worst-case) **Best Observable Selection** problem (Definition A.1) a learner is given observables $0\preceq A_1,\dots,A_m\preceq1$ on $\mathbb C^d$ and $n$ copies of an unknown state $\rho$; it measures the copies and outputs $j\in[m]$, with regret $r_\rho(j)=\mu_*-\mu_j$, where $\mu_i=\mathrm{Tr}(\rho A_i)$ and $\mu_*=\max_i\mu_i$.
--
--   **Theorem A.2.** Let $m\ge1$.
--   1. For every $n\ge1$ and all observables $A_1,\dots,A_m$ there is a measurement $M=(M_1,\dots,M_m)$ on $(\mathbb C^d)^{\otimes n}$, chosen without knowledge of $\rho$, such that for every state $\rho$
--   $$\mathbb E_{j\sim M(\rho^{\otimes n})}[r_\rho(j)]\le\sqrt{\frac{\ln m}{2n}}.$$
--   2. Consequently, for every $\varepsilon>0$ and every $n\ge\frac{\ln m}{2\varepsilon^2}$ there is such a measurement with expected regret at most $\varepsilon$ at every state.
--
--   This is an "argmax" version of shadow tomography, essentially equivalent to Threshold Search, and gives a route to $\log m$ dependence in offline shadow tomography.
--
--   **Formalization Note** A learner is a POVM with outcomes `Fin m` on the $n$-copy register; adaptive measurements and internal randomness compose into one POVM. $\ln$ is the natural logarithm.
--
--   Differences from the source:
--   - reading: There is a Best Observable Selection algorithm with expected regret at most √(ln m/2n) → clause (i): ∃ M, ∀ density ρ, expectedRegret ≤ √(ln m/(2n)) (M chosen before ρ); reason: Definition A.1 is the worst-case problem: the learner does not know ρ
--   - encoding: a Best Observable Selection algorithm (measure the n copies and output j ∈ [m]) → a POVM M : Fin m → operators on (ℂ^d)^{⊗n} (FuchsVdGraaf.IsPOVM: each M_j positive semidefinite, ∑ M_j = 1), depending on d, m, n and the A_i but not on ρ; reason: adaptive measurements and internal randomness compose into one POVM, so every algorithm is of this form; outputs [m] are indexed by Fin m
--   - encoding: √(ln m/2n) → Real.sqrt (Real.log m / (2 * n)) with n ≥ 1 in clause (i); reason: ln is the natural logarithm; the expression is undefined at n = 0 (Lean's x/0 = 0 would make the bound 0)
--   - encoding: Thus the expected regret is at most ε provided n ≥ ln m/2ε² → clause (ii): for every ε > 0 and every n with Real.log m / (2 ε²) ≤ n, ∃ M, ∀ density ρ, expectedRegret ≤ ε; reason: ln m/2ε² read as ln m/(2ε²); ε > 0 is the error parameter of Definition 1.1; at n = 0 the hypothesis forces m = 1, where the claim holds
--   - encoding: observables A_1, …, A_m with μ_* := max_i μ_i and output j ∈ [m] → m ≥ 1, μ_* = ⨆ over Fin m; reason: a maximum and an output index need [m] nonempty; over a finite nonempty index set the supremum is the maximum
--   - encoding: expected regret E_{j∼M(ρ^{⊗n})}[r_ρ(j)] → expectedRegret A M ρ = ∑_j Tr(M_j ρ^{⊗n}) (μ_* − μ_j); reason: definition of the expectation over the outcome distribution of a finite POVM
--   - encoding: Tr(·) of the product → the real part .trace.re; reason: every such trace is of a positive semidefinite operator or of a product of two Hermitian operators, so it is real and the real part is its value
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Theorem A.2, p. 25

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_OnlineShadow_LogRate_Supplement_expectedRegret

open scoped ComplexOrder

namespace OnlineShadow.LogRate.Supplement

/-- **Theorem A.2** (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), p.25). There is a Best Observable Selection algorithm with expected regret at
most `√(ln m/2n)`. Thus the expected regret is at most `ε` provided `n ≥ ln m/2ε²`.

(i) For every `d`, `m ≥ 1`, `n ≥ 1` and effects `0 ⪯ A₁, …, A_m ⪯ 1` on `ℂ^d` there is a POVM
`M = (M₁, …, M_m)` on `(ℂ^d)^{⊗n}`, chosen before the state, whose expected regret at every density matrix
`ρ` is at most `√(ln m/(2n))`.
(ii) For every `ε > 0` and every `n` with `ln m/(2ε²) ≤ n` there is such a POVM with expected regret at
most `ε` at every density matrix `ρ`.

**Formalization Note** "Best Observable Selection algorithm" (Definition A.1) is a POVM with outcomes
`Fin m` on the `n`-copy register (`FuchsVdGraaf.IsPOVM`: each element positive semidefinite, sum the
identity); adaptive measurements and internal randomness compose into one POVM. `ln` is `Real.log`. The
bound `√(ln m/2n)` is read as `√(ln m/(2n))`; `n ≥ 1` in (i) because the bound is undefined at
`n = 0`. `m ≥ 1` because the output is an index `j ∈ [m]` and `μ_*` is a maximum. -/
theorem theorem_A_2 :
    (∀ (d m n : ℕ), 1 ≤ m → 1 ≤ n →
      ∀ A : Fin m → Matrix (Fin d) (Fin d) ℂ, (∀ i, ShadowTomography.UpperBound.IsEffect (A i)) →
        ∃ M : Fin m → Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ, FuchsVdGraaf.IsPOVM M ∧
          ∀ ρ : Matrix (Fin d) (Fin d) ℂ, WildeQIT.IsDensityOperator ρ →
            expectedRegret A M ρ ≤ Real.sqrt (Real.log m / (2 * n))) ∧
    (∀ (d m n : ℕ) (ε : ℝ), 1 ≤ m → 0 < ε → Real.log m / (2 * ε ^ 2) ≤ n →
      ∀ A : Fin m → Matrix (Fin d) (Fin d) ℂ, (∀ i, ShadowTomography.UpperBound.IsEffect (A i)) →
        ∃ M : Fin m → Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ, FuchsVdGraaf.IsPOVM M ∧
          ∀ ρ : Matrix (Fin d) (Fin d) ℂ, WildeQIT.IsDensityOperator ρ →
            expectedRegret A M ρ ≤ ε) := by sorry

end OnlineShadow.LogRate.Supplement
