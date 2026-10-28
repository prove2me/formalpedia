-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_centered_approx_eigenfunction_readable
-- name    : FunctionalInequalities.KLS.LogConcave.exists_centered_approx_eigenfunction_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:52.124181+00:00
-- url     : https://prove2.me/theorems/04df69bd-1e03-46e7-9e06-424aceed0f6e
-- title:
--   Centered Approximate First Eigenfunction
-- statement:
--   This statement constructs approximate first eigenfunctions in the heat model.
--
--   Let $V$ be a finite-dimensional real inner-product space, let $\nu$ be log-concave with nonempty support interior, and suppose
--   $$\nu=m.\operatorname{tilted}(-U),$$
--   where $U$ is twice continuously differentiable. Let $C>0$ satisfy $C_P(\nu)=C$. For every $\eta>0$, there exists an element $f$ in the domain of the adjoint composition of the closed weighted gradient such that
--   $$\operatorname{mean}_\nu(f)=0,\qquad \|f\|=1,$$
--   and
--   $$\|A f-C^{-1}f\|\le C^{-1}\eta,$$
--   where $A=\overline{\nabla}^{\,\dagger}\overline{\nabla}$ is represented by `adjointComp`.
--
--   The result provides an approximate, rather than exact, first eigenfunction for arguments that do not assume compact resolvent or eigenvalue attainment.
--
--   **Formalization Note.** The equality $C_P(\nu)=C$ is in `ENNReal`; $C^{-1}$ and the residual norm are real-valued.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_centered_approx_eigenfunction {C : NNReal} (hC : 0 < C)
--       (hCP : Poincare.LocalSlope.Intrinsic.constant ν = (C : ENNReal)) {η : ℝ} (hη : 0 < η) :
--       ∃ f : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain,
--         L2.mean ν (f : Lp ℝ 2 (ν : Measure V)) = 0 ∧ ‖(f : Lp ℝ 2 (ν : Measure V))‖ = 1 ∧
--         ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) f -
--             (C : ℝ)⁻¹ • (f : Lp ℝ 2 (ν : Measure V))‖ ≤ (C : ℝ)⁻¹ * η
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/ApproximateEigenfunction`](https://prove2.me/theorems/c5bf48cd-81f9-4528-8e4e-dd3378a514bf).
--
--   Definition modules: [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8), [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Poincare/LocalSlope/Basic`](https://prove2.me/theorems/4e65eb6a-acd3-4142-85a9-b5d14c62f3d1).
--
--   Supporting theorems: [`exists_approx_eigenvector_of_gap`](https://prove2.me/theorems/96ac6eeb-d36c-4b96-80f6-6688bd059a47), [`closedWeightedOperator_id_gap_of_literature_le`](https://prove2.me/theorems/09f3e596-c3fd-4ea9-94f3-e85e0a602693), [`orthogonal_ker_iff_mean_eq_zero`](https://prove2.me/theorems/10368e04-91d8-41a4-9291-f17015f3bc65), [`exists_centered_unit_near_optimal`](https://prove2.me/theorems/b05f5b48-2816-4781-a9a1-de8f68e6e8d4).
--
--   Previous: [`exists_centered_unit_near_optimal`](https://prove2.me/theorems/b05f5b48-2816-4781-a9a1-de8f68e6e8d4).
--
--   [Source excerpt, lines 100–105](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/ApproximateEigenfunction.lean#L100-L105) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/ApproximateEigenfunction.lean#L96-L161 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.ApproximateEigenfunction`, declaration `FunctionalInequalities.KLS.LogConcave.exists_centered_approx_eigenfunction`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_ApproximateEigenfunction

open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.Semigroup.Generated
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty)
variable {U : V → ℝ} (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
include hνU hU

theorem FunctionalInequalities.KLS.LogConcave.exists_centered_approx_eigenfunction_readable {C : NNReal} (hC : 0 < C)
    (hCP : Poincare.LocalSlope.Intrinsic.constant ν = (C : ENNReal)) {η : ℝ} (hη : 0 < η) :
    ∃ f : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain,
      L2.mean ν (f : Lp ℝ 2 (ν : Measure V)) = 0 ∧ ‖(f : Lp ℝ 2 (ν : Measure V))‖ = 1 ∧
      ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) f -
          (C : ℝ)⁻¹ • (f : Lp ℝ 2 (ν : Measure V))‖ ≤ (C : ℝ)⁻¹ * η := by sorry
