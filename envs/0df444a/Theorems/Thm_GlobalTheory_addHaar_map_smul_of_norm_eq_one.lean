-- Prove2me | Theorems.Thm_GlobalTheory_addHaar_map_smul_of_norm_eq_one
-- name    : GlobalTheory.addHaar_map_smul_of_norm_eq_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:04:30.545254+00:00
-- url     : https://prove2.me/theorems/57b3a6a4-2d8d-47de-a46c-9607215c3ba4
-- title:
--   Global Theory: add Haar map smul of norm eq one
-- statement:
--   The Global Theory construction uses the add Haar map smul of norm eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/AddHaarMapSmulOfNormEqOne.lean#L6-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/AddHaarMapSmulOfNormEqOne.lean#L6-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AddHaarMapSmulOfNormEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open GlobalTheory

theorem GlobalTheory.addHaar_map_smul_of_norm_eq_one (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (c : K) (hc : ‖c‖ = 1) : Measure.map (fun x : V => c • x) μ = μ := by sorry
