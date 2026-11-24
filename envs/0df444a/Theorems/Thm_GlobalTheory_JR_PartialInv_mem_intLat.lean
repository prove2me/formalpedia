-- Prove2me | Theorems.Thm_GlobalTheory_JR_PartialInv_mem_intLat
-- name    : GlobalTheory.JR.PartialInv.mem_intLat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:34:37.42691+00:00
-- url     : https://prove2.me/theorems/90e21d1b-41a6-41f9-baad-28e9e94f4ef3
-- title:
--   Partial Inv: mem int Lat
-- statement:
--   The Partial Inv construction uses the mem int Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MixedModelPartialFourierColumnTwiceNegColumn.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MixedModelPartialFourierColumnTwiceNegColumn.lean#L26-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelPartialFourierColumnTwiceNegColumn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.PartialInv

theorem GlobalTheory.JR.PartialInv.mem_intLat {F : Type} [NormedField F] [IsUltrametricDist F] {r : ℕ} (x : Fin r → F) :
    x ∈ intLat F r ↔ ∀ i, ‖x i‖ ≤ 1 := by sorry
