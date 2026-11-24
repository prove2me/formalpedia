-- Prove2me | Theorems.Thm_GlobalTheory_TestLat_weyl_rowAct_mem_of_isUnit_det
-- name    : GlobalTheory.TestLat.weyl_rowAct_mem_of_isUnit_det
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:03:37.904829+00:00
-- url     : https://prove2.me/theorems/a4d96a24-08fd-4d8a-8f7a-8dc74b77cc36
-- title:
--   Test Lat: weyl row Act mem of is Unit det
-- statement:
--   The Test Lat construction uses the weyl row Act mem of is Unit det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/WeylRowActMemOfIsUnitDet.lean#L6-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/WeylRowActMemOfIsUnitDet.lean#L6-L13

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_WeylRowActMemOfIsUnitDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TestLat

theorem GlobalTheory.TestLat.weyl_rowAct_mem_of_isUnit_det :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) (ν : Fin n → ℕ), Antitone ν →
      ∀ g : Matrix (Fin n) (Fin n) R, IsUnit g.det →
        ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R n n (le_refl n) ν,
          Formalism.GradedWeylDivisibility.rowAct R g f ∈ Formalism.GradedWeylDivisibility.weyl R n n (le_refl n) ν := by sorry
