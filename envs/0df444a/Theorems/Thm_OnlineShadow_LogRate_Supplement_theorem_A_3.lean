-- Prove2me | Theorems.Thm_OnlineShadow_LogRate_Supplement_theorem_A_3
-- name    : OnlineShadow.LogRate.Supplement.theorem_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:56:57.7466+00:00
-- url     : https://prove2.me/theorems/c0a1c011-7541-458c-aa57-72b144862011
-- title:
--   Theorem A.3 — Bayesian Best Observable Selection with expected regret $\le\sqrt{\ln m/2n}$
-- statement:
--   In the **Bayesian** version of Best Observable Selection the learner is given observables $0\preceq A_1,\dots,A_m\preceq1$ on $\mathbb C^d$ and a known distribution $\mathcal D$ on states; a state $\rho\sim\mathcal D$ is drawn, the learner measures $\rho^{\otimes n}$ and outputs $j\in[m]$, with regret $r_\rho(j)=\mu_*-\mu_j$, $\mu_i=\mathrm{Tr}(\rho A_i)$, $\mu_*=\max_i\mu_i$.
--
--   **Theorem A.3.** Let $m\ge1$ and $n\ge1$. For all observables $A_1,\dots,A_m$ and every probability distribution $\mathcal D$ on $d\times d$ density matrices there is a measurement $M=(M_1,\dots,M_m)$ on $(\mathbb C^d)^{\otimes n}$, depending only on $\mathcal D$ and $A_1,\dots,A_m$, such that
--   $$\mathop{\mathbb E}_{\substack{\rho\sim\mathcal D\\ j\sim M(\rho^{\otimes n})}}[r_\rho(j)]\le\sqrt{\frac{\ln m}{2n}}.$$
--
--   By the minimax theorem for bilinear games on convex compact sets this is equivalent to Theorem A.2 (p. 25 of the paper).
--
--   **Formalization Note** $\mathcal D$ is an arbitrary probability measure on the space of $d\times d$ complex matrices with its Borel σ-algebra, concentrated on density matrices. The expectation is the integral over $\mathcal D$ of the expected regret at $\rho$. $\ln$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: a known distribution D on states → a probability measure D on d × d complex matrices (any σ-algebra that is the Borel σ-algebra) with D-almost every ρ a density matrix; reason: a distribution on the set of states is the same as a probability measure on the matrix space concentrated on states; D is otherwise arbitrary (not finitely supported, no density)
--   - encoding: E_{ρ∼D, j∼M(ρ⊗n)}[r_ρ(j)] → ∫ expectedRegret A M ρ dD(ρ); reason: iterated expectation; the integrand is continuous in ρ and lies in [0,1] on states, so the Bochner integral is the genuine expectation
--   - encoding: a POVM M (depending only on D and A_1, … A_m) → ∃ M : Fin m → operators on (ℂ^d)^{⊗n} with FuchsVdGraaf.IsPOVM M, quantified after D and A (and d, m, n); reason: the POVM may depend on D and the observables but not on the drawn ρ; outputs [m] are indexed by Fin m
--   - encoding: √(ln m/2n) → Real.sqrt (Real.log m / (2 * n)) with n ≥ 1; reason: ln is the natural logarithm; the expression is undefined at n = 0 (Lean's x/0 = 0 would make the bound 0)
--   - encoding: observables A_1, …, A_m with μ_* := max_i μ_i and output j ∈ [m] → m ≥ 1, μ_* = ⨆ over Fin m; reason: a maximum and an output index need [m] nonempty; over a finite nonempty index set the supremum is the maximum
--   - encoding: expected regret E_{j∼M(ρ^{⊗n})}[r_ρ(j)] → expectedRegret A M ρ = ∑_j Tr(M_j ρ^{⊗n}) (μ_* − μ_j); reason: definition of the expectation over the outcome distribution of a finite POVM
--   - encoding: Tr(·) of the product → the real part .trace.re; reason: every such trace is of a positive semidefinite operator or of a product of two Hermitian operators, so it is real and the real part is its value
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Theorem A.3, p. 25

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_OnlineShadow_LogRate_Supplement_expectedRegret

open scoped ComplexOrder
open MeasureTheory

namespace OnlineShadow.LogRate.Supplement

/-- **Theorem A.3** (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), p.25). Consider a Bayesian version of Best Observable Selection, with input
including a known distribution `D` on states. Then there is a POVM `M` (depending only on `D` and
`A₁, …, A_m`) satisfying `E_{ρ∼D, j∼M(ρ^{⊗n})}[r_ρ(j)] ≤ √(ln m/2n)`.

For every `d`, `m ≥ 1`, `n ≥ 1`, effects `0 ⪯ A₁, …, A_m ⪯ 1` on `ℂ^d` and every probability measure
`D` on `d × d` complex matrices concentrated on density matrices, there is a POVM `M` on `(ℂ^d)^{⊗n}`
with outcomes `Fin m` such that `∫ E_{j∼M(ρ^{⊗n})}[r_ρ(j)] dD(ρ) ≤ √(ln m/(2n))`.

**Formalization Note** The matrix space carries any σ-algebra that is its Borel σ-algebra
(`[BorelSpace]`); `D` is an arbitrary probability measure with `D`-almost every `ρ` a density matrix
(not necessarily finitely supported or with a density). The integrand is continuous in `ρ` and lies in
`[0, 1]` on density matrices, so the integral is a genuine expectation. `M` is chosen after `D` and
`A`. `ln` is `Real.log`; `√(ln m/2n)` is read as `√(ln m/(2n))`; `n ≥ 1` and `m ≥ 1` as in
Theorem A.2. -/
theorem theorem_A_3 (d m n : ℕ) [MeasurableSpace (Matrix (Fin d) (Fin d) ℂ)]
    [BorelSpace (Matrix (Fin d) (Fin d) ℂ)] (hm : 1 ≤ m) (hn : 1 ≤ n)
    (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, ShadowTomography.UpperBound.IsEffect (A i))
    (D : Measure (Matrix (Fin d) (Fin d) ℂ)) [IsProbabilityMeasure D]
    (hD : ∀ᵐ ρ ∂D, WildeQIT.IsDensityOperator ρ) :
    ∃ M : Fin m → Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ, FuchsVdGraaf.IsPOVM M ∧
      ∫ ρ, expectedRegret A M ρ ∂D ≤ Real.sqrt (Real.log m / (2 * n)) := by sorry

end OnlineShadow.LogRate.Supplement
