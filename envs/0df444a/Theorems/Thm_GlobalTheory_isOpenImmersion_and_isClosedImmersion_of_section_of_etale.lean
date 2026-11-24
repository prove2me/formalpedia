-- Prove2me | Theorems.Thm_GlobalTheory_isOpenImmersion_and_isClosedImmersion_of_section_of_etale
-- name    : GlobalTheory.isOpenImmersion_and_isClosedImmersion_of_section_of_etale
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:57:49.289147+00:00
-- url     : https://prove2.me/theorems/abfba430-97ce-4b91-83b1-8dc8a3312329
-- title:
--   Global Theory: is Open Immersion and is Closed Immersion of section of etale
-- statement:
--   The Global Theory construction uses the is Open Immersion and is Closed Immersion of section of etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L122-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L122-L126

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

theorem GlobalTheory.isOpenImmersion_and_isClosedImmersion_of_section_of_etale {X S : Scheme.{u}} (f : X ⟶ S)
    [Etale f] [IsSeparated f] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) :
    IsOpenImmersion s ∧ IsClosedImmersion s := by sorry
