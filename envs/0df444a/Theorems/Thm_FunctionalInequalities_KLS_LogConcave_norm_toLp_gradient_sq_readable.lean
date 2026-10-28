-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_norm_toLp_gradient_sq_readable
-- name    : FunctionalInequalities.KLS.LogConcave.norm_toLp_gradient_sq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:10.055984+00:00
-- url     : https://prove2.me/theorems/08f6268b-f9f3-4fc1-9889-3665ced688d5
-- title:
--   Gradient Class Norm Equals Dirichlet Energy
-- statement:
--   This statement identifies the squared $L^2(\nu)$ norm of a classical gradient with its integrated Dirichlet energy.
--
--   Let $V$ be a complete real inner-product space with the stated measurable and second-countable structures, let $\nu$ be a probability measure, and let $f:V\to\mathbb R$ be smooth of class $C^\infty$ with compact support. Then
--   $$\|[\nabla f]_{L^2(\nu)}\|^2
--   =\int_V\|\nabla f(x)\|^2\,d\nu(x)
--   =\int_V\Gamma(f,f)(x)\,d\nu(x).$$
--
--   The identity supplies the standard correspondence between the $L^2$ gradient norm and the Dirichlet energy in the heat-semigroup formalization.
--
--   **Formalization Note.** No finite-dimensionality assumption is present in the declaration. The gradient class is obtained through `MemLp.toLp`; the integrals are ordinary real-valued integrals.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_toLp_gradient_sq {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
--       ‖(memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) hf hfc).toLp (gradient f)‖ ^ 2 =
--         ∫ x, gamma f f x ∂(ν : Measure V)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/Curvature`](https://prove2.me/theorems/cf9c6f61-3825-46e6-acd2-1e708f058970).
--
--   Definition modules: [`Analysis/BakryEmery/Gamma`](https://prove2.me/theorems/6b6aef00-0f84-4633-a830-e04239f02b6b), [`KLS/LogConcave/HeatSemigroup/Generator`](https://prove2.me/theorems/1303b530-0417-4686-98e2-cba0795ab727).
--
--   Next: [`mul_norm_closedWeightedOperator_toLp_sq_le`](https://prove2.me/theorems/1216a9e9-dda9-49e5-b0a6-d2e0cf7acb3e).
--
--   [Source excerpt, lines 52–54](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Curvature.lean#L52-L54) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Curvature.lean#L50-L73 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Curvature`, declaration `FunctionalInequalities.KLS.LogConcave.norm_toLp_gradient_sq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature

open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
omit [FiniteDimensional ℝ V]

theorem FunctionalInequalities.KLS.LogConcave.norm_toLp_gradient_sq_readable {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ‖(memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) hf hfc).toLp (gradient f)‖ ^ 2 =
      ∫ x, gamma f f x ∂(ν : Measure V) := by sorry
