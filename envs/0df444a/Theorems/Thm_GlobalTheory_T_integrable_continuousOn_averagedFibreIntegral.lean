-- Prove2me | Theorems.Thm_GlobalTheory_T_integrable_continuousOn_averagedFibreIntegral
-- name    : GlobalTheory.T.integrable_continuousOn_averagedFibreIntegral
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:47:31.162428+00:00
-- url     : https://prove2.me/theorems/80ca803b-309b-4193-875a-2196d49acc0f
-- title:
--   T: integrable continuous On averaged Fibre Integral
-- statement:
--   The T construction uses the integrable continuous On averaged Fibre Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IntegrableContinuousOnAveragedFibreIntegralStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IntegrableContinuousOnAveragedFibreIntegralStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegrableContinuousOnAveragedFibreIntegral
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FibOfZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegrableContinuousOnAveragedFibreIntegralStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.integrable_continuousOn_averagedFibreIntegral : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K), Continuous q → (∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x) → ∀ (U : Set K) (s : K → K), GlobalTheory.QuadFibre.IsSqrtOn U s → ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → (∀ t : K, t ≠ 0 → Integrable φ (GlobalTheory.QuadFibre.fibOf μ ν q U s t)) ∧ ContinuousOn (fun t => ∫ x, φ x ∂(GlobalTheory.QuadFibre.fibOf μ ν q U s t)) {t : K | t ≠ 0} := by sorry
