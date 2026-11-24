-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_map_maximalIdeal
-- name    : GlobalTheory.UnitLemma.Unr.map_maximalIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:13:28.758076+00:00
-- url     : https://prove2.me/theorems/70466c1f-2769-42cd-9cf0-e2047f4aa338
-- title:
--   Unr: map maximal Ideal
-- statement:
--   The Unr construction uses the map maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitTraceUnramifiedExtension.lean#L82-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitTraceUnramifiedExtension.lean#L82-L89

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

theorem GlobalTheory.UnitLemma.Unr.map_maximalIdeal (hU : IsUnrExt K K' d φ) :
    Ideal.map (intMap hU) (IsLocalRing.maximalIdeal K.O) = IsLocalRing.maximalIdeal K'.O := by sorry
