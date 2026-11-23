-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_intMap_spec
-- name    : GlobalTheory.UnitLemma.Unr.intMap_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:13:35.134801+00:00
-- url     : https://prove2.me/theorems/d1601228-e688-4de9-af7e-a5e2a6223390
-- title:
--   Unr: int Map spec
-- statement:
--   The Unr construction uses the int Map spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitTraceUnramifiedExtension.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitTraceUnramifiedExtension.lean#L31-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerSpanningFamilyOfUnramifiedExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitTraceUnramifiedExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial
variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}

theorem GlobalTheory.UnitLemma.Unr.intMap_spec (hU : IsUnrExt K K' d φ) (a : K.O) :
    algebraMap K'.O K'.E (intMap hU a) = φ (algebraMap K.O K.E a) := by sorry
