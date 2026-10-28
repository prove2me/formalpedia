-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_taylorCriterion_readable
-- name    : FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorCriterion_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:19:07.096617+00:00
-- url     : https://prove2.me/theorems/02b2baa1-1cb3-4817-9e35-5dc605a75700
-- title:
--   Taylor-Coefficient Criterion For The Poincaré Constant
-- statement:
--   Let $V$ be finite-dimensional, let $\nu$ be log-concave with nonempty support interior, and let $m$ be an additive Haar measure. Let $U:V\to\mathbb R$ have temperate growth and satisfy
--   $$\nu=m.\operatorname{tilted}(-U),$$
--   with all exponential moments finite. Assume:
--   1. $U$ has Hessian lower bound $D^2U(x)[v,v]\ge a\|v\|^2$ for some $a>0$ and all $x,v$;
--   2. $\int\langle v,x\rangle^2\,d\nu(x)\le\|v\|^2$ for every $v\in V$;
--   3. $R\ge1$; and
--   4. for every $u\in L^2(\nu)$ and every $d\ge1$, the Taylor bound
--   $$\|T_du\|\le R^d\|u\|$$
--   holds in the standard-basis Hilbert–Schmidt norm.
--
--   Then
--   $$C_P(\nu)\le\operatorname{ofReal}(K R^2),$$
--   where $K$ is `taylorCriterionConstant`.
--
--   This is the principal criterion converting uniform Taylor-coefficient control into a Poincaré bound under the stated heat-model hypotheses. It is a finite-dimensional, measure-specific implication rather than a dimension-free universal assertion.
--
--   **Formalization Note.** The conclusion is an `ENNReal` inequality, expressed using `ENNReal.ofReal`; the covariance condition is stated without an explicit centering assumption.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.PoissonIterate`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem taylorCriterion
--       (hνU : (ν : Measure V) = m.tilted (-U)) (hU : U.HasTemperateGrowth)
--       (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
--       {a : ℝ} (ha : 0 < a) (hUa : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
--       (hcov : ∀ v : V, ∫ x, ⟪v, x⟫ ^ 2 ∂(ν : Measure V) ≤ ‖v‖ ^ 2)
--       {R : ℝ} (hR : 1 ≤ R)
--       (h29 : ∀ (u : Lp ℝ 2 (ν : Measure V)) (d : ℕ), 1 ≤ d →
--         ‖coordTensor (stdOrthonormalBasis ℝ V) (taylorTensor (ν : Measure V) (⇑u) d)‖ ≤
--           R ^ d * ‖u‖) :
--       Poincare.LocalSlope.Intrinsic.constant ν ≤
--         ENNReal.ofReal (taylorCriterionConstant * R ^ 2)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/PoissonIterate/Criterion`](https://prove2.me/theorems/b6210dc1-894e-490a-a262-24735151f6b5).
--
--   Definition modules: [`Analysis/Tensor/Coefficients`](https://prove2.me/theorems/88ad50f9-51e6-4e95-905e-5bcdc077739f), [`Analysis/Tensor/Coordinate`](https://prove2.me/theorems/024d1767-7544-4265-9acb-d8fe6f0df92f), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a), [`Poincare/LocalSlope/Basic`](https://prove2.me/theorems/4e65eb6a-acd3-4142-85a9-b5d14c62f3d1).
--
--   Selected supporting theorems: [`integral_hessianSq_add_le_of_hasTemperateGrowth`](https://prove2.me/theorems/fcac2fc2-d13a-43a7-b290-c7c1b8a429f0), [`summable_and_tendsto_zero_of_energy`](https://prove2.me/theorems/4b5372cd-579f-4bd0-914c-123a1ea1de17), [`taylorTensor_const_mul`](https://prove2.me/theorems/7da0a874-3260-449d-b383-221740a01959), [`inv_le_scale_sq_step`](https://prove2.me/theorems/f9eabf78-c00a-4ef8-a681-0262f5a3b540), [`le_of_iterate_bounds`](https://prove2.me/theorems/f80538b2-5d61-41ae-9ced-cdc9bb4e7bf2).
--
--   Previous: [`norm_taylorField_sq_le`](https://prove2.me/theorems/658d541a-caf2-439c-ac49-7e33a7865643).
--
--   [Source excerpt, lines 489–499](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Criterion.lean#L489-L499) · Frozen source `408915f`.
--
--   **Literature**
--
--   This formalizes Theorem 3.1 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), p. 10.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Criterion.lean#L478-L512 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.Criterion`, declaration `FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorCriterion`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Criterion

open MeasureTheory Filter Topology Finset
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped ENNReal NNReal RealInnerProductSpace InnerProductSpace ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
include hν hi

theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorCriterion_readable
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : U.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    {a : ℝ} (ha : 0 < a) (hUa : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (hcov : ∀ v : V, ∫ x, ⟪v, x⟫ ^ 2 ∂(ν : Measure V) ≤ ‖v‖ ^ 2)
    {R : ℝ} (hR : 1 ≤ R)
    (h29 : ∀ (u : Lp ℝ 2 (ν : Measure V)) (d : ℕ), 1 ≤ d →
      ‖coordTensor (stdOrthonormalBasis ℝ V) (taylorTensor (ν : Measure V) (⇑u) d)‖ ≤
        R ^ d * ‖u‖) :
    Poincare.LocalSlope.Intrinsic.constant ν ≤
      ENNReal.ofReal (taylorCriterionConstant * R ^ 2) := by sorry
