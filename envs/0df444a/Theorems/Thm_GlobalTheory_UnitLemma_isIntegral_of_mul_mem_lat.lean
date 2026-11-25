-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_isIntegral_of_mul_mem_lat
-- name    : GlobalTheory.UnitLemma.isIntegral_of_mul_mem_lat
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:54:34.249229+00:00
-- url     : https://prove2.me/theorems/679291cd-9cd2-4b0d-8597-ca411962ef0e
-- title:
--   Unit Lemma: is Integral of mul mem lat
-- statement:
--   The Unit Lemma construction uses the is Integral of mul mem lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/StabilizerStableLatticeLeIntegralUnitsSubgroup.lean#L12-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/StabilizerStableLatticeLeIntegralUnitsSubgroup.lean#L12-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StabilizerStableLatticeLeIntegralUnitsSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma
open Polynomial
variable {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A]

theorem GlobalTheory.UnitLemma.isIntegral_of_mul_mem_lat {L : Submodule O A} (hL : IsLat O E L) (t : A)
    (ht : ∀ y ∈ L, t * y ∈ L) : IsIntegral O t := by sorry
