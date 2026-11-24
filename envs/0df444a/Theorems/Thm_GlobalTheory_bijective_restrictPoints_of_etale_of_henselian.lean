-- Prove2me | Theorems.Thm_GlobalTheory_bijective_restrictPoints_of_etale_of_henselian
-- name    : GlobalTheory.bijective_restrictPoints_of_etale_of_henselian
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:06:45.892255+00:00
-- url     : https://prove2.me/theorems/39c3e519-bf04-4356-8696-67cfcf39b7e2
-- title:
--   Global Theory: bijective restrict Points of etale of henselian
-- statement:
--   The Global Theory construction uses the bijective restrict Points of etale of henselian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L360-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L360-L365

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory

theorem GlobalTheory.bijective_restrictPoints_of_etale_of_henselian {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]
    (R : Type u) [CommRing R] [HenselianLocalRing R] (h : Spec (.of R) ⟶ S) :
    Function.Bijective (restrictPoints f h
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) := by sorry
