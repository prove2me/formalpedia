-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_exists_int_basis_of_unr
-- name    : GlobalTheory.UnitLemma.Unr.exists_int_basis_of_unr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:21.144152+00:00
-- url     : https://prove2.me/theorems/373431bb-7b42-4145-a3b2-41a268e30006
-- title:
--   Unr: exists int basis of unr
-- statement:
--   The Unr construction uses the exists int basis of unr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegerSpanningFamilyOfUnramifiedExt.lean#L37-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegerSpanningFamilyOfUnramifiedExt.lean#L37-L148

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

theorem GlobalTheory.UnitLemma.Unr.exists_int_basis_of_unr (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ) :
    ∃ u : Fin d → K'.O, ∀ y : K'.O, ∃ a : Fin d → K.O,
      algebraMap K'.O K'.E y = ∑ i, φ (algebraMap K.O K.E (a i)) * algebraMap K'.O K'.E (u i) := by sorry
