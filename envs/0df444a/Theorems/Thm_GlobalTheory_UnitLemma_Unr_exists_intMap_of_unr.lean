-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_exists_intMap_of_unr
-- name    : GlobalTheory.UnitLemma.Unr.exists_intMap_of_unr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:09:34.525218+00:00
-- url     : https://prove2.me/theorems/4018e33f-2e7e-4756-a4d6-807e3ac52141
-- title:
--   Unr: exists int Map of unr
-- statement:
--   The Unr construction uses the exists int Map of unr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegerSpanningFamilyOfUnramifiedExt.lean#L26-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegerSpanningFamilyOfUnramifiedExt.lean#L26-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerSpanningFamilyOfUnramifiedExt
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
open GlobalTheory.UnitLemma IsDedekindDomain IsLocalRing
variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}

theorem GlobalTheory.UnitLemma.Unr.exists_intMap_of_unr (hU : IsUnrExt K K' d φ) :
    ∃ ψ : K.O →+* K'.O, ∀ a, algebraMap K'.O K'.E (ψ a) = φ (algebraMap K.O K.E a) := by sorry
