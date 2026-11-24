-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Orbit_coe_mulLat_of_coe_eq
-- name    : GlobalTheory.UnitLemma.Orbit.coe_mulLat_of_coe_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:29:07.395234+00:00
-- url     : https://prove2.me/theorems/2bfc7c07-3287-42fd-8239-e1aa825bd9bb
-- title:
--   Orbit: coe mul Lat of coe eq
-- statement:
--   The Orbit construction uses the coe mul Lat of coe eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeightedOrbitSumCongrCoefficientRing.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeightedOrbitSumCongrCoefficientRing.lean#L11-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeightedOrbitSumCongrCoefficientRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit
open GlobalTheory.UnitLemma

theorem GlobalTheory.UnitLemma.Orbit.coe_mulLat_of_coe_eq {O O' A : Type} [CommRing O] [CommRing O'] [CommRing A] [Algebra O A]
    [Algebra O' A] (L : Submodule O A) (L' : Submodule O' A) (h : (L' : Set A) = L) (t : Aˣ) :
    (mulLat O' (t : A) L' : Set A) = mulLat O (t : A) L := by sorry
