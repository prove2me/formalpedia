-- Prove2me | Theorems.Thm_GenEmpLik_Consistency_theorem_7
-- name    : GenEmpLik.Consistency.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:14:29.118985+00:00
-- url     : https://prove2.me/theorems/470f13de-9d41-44c0-91c9-97f0b400deca
-- title:
--   Theorem 7 — the f-divergence robust objective converges uniformly to E_{P₀}[ℓ(x; ξ)] almost surely
-- statement:
--   Let $\xi_1,\xi_2,\dots$ be i.i.d. random elements of a separable metric space $\Xi$ with law $P_0$, let $\widehat P_n$ be the empirical distribution of the first $n$, and let $\mathcal X\subset\mathbb R^d$ be nonempty and closed. Let $\ell$ be lower semicontinuous on $\mathcal X\times\Xi$ and $\ell(x;\cdot)$ measurable for each $x\in\mathcal X$. Let $f$ satisfy Assumption A, let $\rho\ge0$, let Assumption E hold, and assume the class $\{\ell(x;\cdot):x\in\mathcal X\}$ is Glivenko–Cantelli. Then
--
--   $$
--   \sup_{x\in\mathcal X}\ \sup_{P\ll\widehat P_n}\Big\{\big|E_P[\ell(x;\xi)]-E_{P_0}[\ell(x;\xi)]\big| : D_f\big(P\|\widehat P_n\big)\le\frac{\rho}{n}\Big\}\ \xrightarrow{\ \text{a.s.}^*\ }\ 0 .
--   $$
--
--   Thus the robust objective, and every reweighting in the $\rho/n$ divergence ball, converges to the population risk uniformly over the decision set, under only slightly more than the first-moment condition needed for sample average approximation.
--
--   **Formalization Note** A distribution $P\ll\widehat P_n$ is a weight vector $p$ on the first $n$ samples $\xi_0,\dots,\xi_{n-1}$ (0-based), feasible when $p\in$ `probUncertaintySet f (1/n,…,1/n) (ρ/n)`. Both suprema are taken in $[0,\infty]$. Almost-sure convergence is `∀ᵐ` (outer measure of the exceptional set is zero), the same reading as in the Glivenko–Cantelli hypothesis. i.i.d. means measurable, mutually independent (`iIndepFun`) and identically distributed with $\xi_0$; $P_0$ is the law of $\xi_0$.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 16, Theorem 7 (proof App. E.1, pp. 46–47)

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_uncertaintySet
import Definitions.Def_GenEmpLik_Coverage_AssumptionA
import Definitions.Def_GenEmpLik_Consistency_AssumptionE
import Definitions.Def_GenEmpLik_Consistency_IsGlivenkoCantelli

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace GenEmpLik.Consistency

/-- Theorem 7 (arXiv:1610.03425v3, p. 16; proof App. E.1, pp. 46–47). Let `ξ₀, ξ₁, …` be
i.i.d. with law `P₀` on a separable metric space, let `f` satisfy Assumption A, `ρ ≥ 0`,
and let `X` be nonempty and closed. Let the lower semicontinuous loss `ℓ` satisfy Assumption E
on `X`, with measurable `ℓ(x; ·)` for `x ∈ X`, and let `{ℓ(x; ·) : x ∈ X}` be
Glivenko–Cantelli. Then, almost surely,
`sup_{x ∈ X} sup { |E_P[ℓ(x; ξ)] − E_{P₀}[ℓ(x; ξ)]| : P ≪ P̂_n, D_f(P ‖ P̂_n) ≤ ρ/n } → 0`,
with `P ≪ P̂_n` the weight vectors `p` on the first `n` samples and the suprema in `[0, ∞]`. -/
theorem theorem_7 {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [MetricSpace Ξ]
    [SecondCountableTopology Ξ]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {d : ℕ}
    (f : ℝ → EReal) (hf : GenEmpLik.Coverage.AssumptionA f) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (ξ : ℕ → Ω → Ξ) (hξm : ∀ i, Measurable (ξ i)) (hξind : iIndepFun ξ μ)
    (hξid : ∀ i, IdentDistrib (ξ i) (ξ 0) μ μ)
    (X : Set (EuclideanSpace ℝ (Fin d))) (hXne : X.Nonempty) (hXclosed : IsClosed X)
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ)
    (hℓlsc : LowerSemicontinuous (fun xs : X × Ξ => ℓ xs.1 xs.2))
    (hℓm : ∀ x ∈ X, Measurable (ℓ x))
    (hE : AssumptionE (μ.map (ξ 0)) X ℓ)
    (hGC : IsGlivenkoCantelli μ ξ ((fun x => ℓ x) '' X)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => ⨆ x ∈ X,
        ⨆ p ∈ PhiDivRobust.Counterpart.probUncertaintySet f (fun _ : Fin n => (1 : ℝ) / n)
          (ρ / n),
        ENNReal.ofReal |∑ i, p i * ℓ x (ξ i ω) - ∫ s, ℓ x s ∂(μ.map (ξ 0))|)
      atTop (𝓝 0) := by sorry

end GenEmpLik.Consistency
