-- Prove2me | Theorems.Thm_GlobalTheory_T_map_smul_addHaar_of_norm_eq_one
-- name    : GlobalTheory.T.map_smul_addHaar_of_norm_eq_one
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:52:33.920115+00:00
-- url     : https://prove2.me/theorems/4c8316a6-a60a-43f3-8d1e-bc4ca7948703
-- title:
--   T: map smul add Haar of norm eq one
-- statement:
--   The T construction uses the map smul add Haar of norm eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/AddHaarMapSmulOfNormEqOneStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/AddHaarMapSmulOfNormEqOneStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AddHaarMapSmulOfNormEqOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AddHaarMapSmulOfNormEqOneStatement
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

theorem GlobalTheory.T.map_smul_addHaar_of_norm_eq_one : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (c : K), ‖c‖ = 1 → Measure.map (fun x : V => c • x) μ = μ := by sorry
