-- Prove2me | Theorems.Thm_GlobalTheory_isOpenImmersion_of_section_of_unramified
-- name    : GlobalTheory.isOpenImmersion_of_section_of_unramified
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:58:05.45994+00:00
-- url     : https://prove2.me/theorems/734b8016-1114-44a8-901c-cb3314538a8a
-- title:
--   Global Theory: is Open Immersion of section of unramified
-- statement:
--   The Global Theory construction uses the is Open Immersion of section of unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L104-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L104-L115

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

theorem GlobalTheory.isOpenImmersion_of_section_of_unramified {X S : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) :
    IsOpenImmersion s := by sorry
