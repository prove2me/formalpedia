-- Prove2me | Theorems.Thm_GlobalTheory_isClosedImmersion_of_section_of_isSeparated
-- name    : GlobalTheory.isClosedImmersion_of_section_of_isSeparated
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:30.20027+00:00
-- url     : https://prove2.me/theorems/26f13121-51ec-4f42-935a-9a8c6e657d4a
-- title:
--   Global Theory: is Closed Immersion of section of is Separated
-- statement:
--   The Global Theory construction uses the is Closed Immersion of section of is Separated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L117-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L117-L120

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

theorem GlobalTheory.isClosedImmersion_of_section_of_isSeparated {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) : IsClosedImmersion s := by sorry
