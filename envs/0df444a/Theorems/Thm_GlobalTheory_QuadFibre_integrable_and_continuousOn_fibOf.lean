-- Prove2me | Theorems.Thm_GlobalTheory_QuadFibre_integrable_and_continuousOn_fibOf
-- name    : GlobalTheory.QuadFibre.integrable_and_continuousOn_fibOf
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:09:37.24608+00:00
-- url     : https://prove2.me/theorems/d824979e-13d6-44d6-b059-5bf729b5e914
-- title:
--   Quad Fibre: integrable and continuous On fib Of
-- statement:
--   The Quad Fibre construction uses the integrable and continuous On fib Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IntegrableContinuousOnAveragedFibreIntegral.lean#L83-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IntegrableContinuousOnAveragedFibreIntegral.lean#L83-L140

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FibOfZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegrableContinuousOnAveragedFibreIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped Pointwise
open GlobalTheory GlobalTheory.QuadFibre

theorem GlobalTheory.QuadFibre.integrable_and_continuousOn_fibOf (K V : Type) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V]
    [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure]
    (q : V → K) (hq : Continuous q) (_hh : ∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x)
    (U : Set K) (s : K → K) (h : IsSqrtOn U s) (φ : V → ℝ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) :
    (∀ t : K, t ≠ 0 → Integrable φ (fibOf μ ν q U s t)) ∧
      ContinuousOn (fun t => ∫ x, φ x ∂(fibOf μ ν q U s t)) {t : K | t ≠ 0} := by sorry
