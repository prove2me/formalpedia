-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilMix_isOpen_setOf_eq_of_isLocallyConstant
-- name    : GlobalTheory.JR.WeilMix.isOpen_setOf_eq_of_isLocallyConstant
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:37:16.171181+00:00
-- url     : https://prove2.me/theorems/4c13e295-1248-430f-bc49-9bfab11c180d
-- title:
--   Weil Mix: is Open set Of eq of is Locally Constant
-- statement:
--   The Weil Mix construction uses the is Open set Of eq of is Locally Constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantCompactSupportMixedModelPartial.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantCompactSupportMixedModelPartial.lean#L17-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportMixedModelPartial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilMix

theorem GlobalTheory.JR.WeilMix.isOpen_setOf_eq_of_isLocallyConstant {Y : Type} [TopologicalSpace Y] {g h : Y → ℂ}
    (hg : IsLocallyConstant g) (hh : IsLocallyConstant h) : IsOpen {p | g p = h p} := by sorry
