-- Prove2me | Theorems.Thm_GlobalTheory_map_comap_maximalIdeal_eq_of_formallyUnramified
-- name    : GlobalTheory.map_comap_maximalIdeal_eq_of_formallyUnramified
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:09:46.577961+00:00
-- url     : https://prove2.me/theorems/b830786e-0739-4138-a2ad-95c4d2458d4e
-- title:
--   Global Theory: map comap maximal Ideal eq of formally Unramified
-- statement:
--   The Global Theory construction uses the map comap maximal Ideal eq of formally Unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapComapMaximalIdealEqOfFormallyUnramified.lean#L7-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapComapMaximalIdealEqOfFormallyUnramified.lean#L7-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapMaximalIdealEqOfFormallyUnramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.map_comap_maximalIdeal_eq_of_formallyUnramified
    (A B : Type) [CommRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
    [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B] :
    ((IsLocalRing.maximalIdeal B).comap (algebraMap A B)).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B := by sorry
