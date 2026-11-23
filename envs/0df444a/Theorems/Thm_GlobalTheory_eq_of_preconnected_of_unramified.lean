-- Prove2me | Theorems.Thm_GlobalTheory_eq_of_preconnected_of_unramified
-- name    : GlobalTheory.eq_of_preconnected_of_unramified
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:08.675305+00:00
-- url     : https://prove2.me/theorems/1c36f9b3-1138-4949-a455-d7ed3d62ee25
-- title:
--   Global Theory: eq of preconnected of unramified
-- statement:
--   The Global Theory construction uses the eq of preconnected of unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L76-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L76-L85

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

theorem GlobalTheory.eq_of_preconnected_of_unramified {X S T Z : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] [IsSeparated f] [PreconnectedSpace T]
    {a b : T ⟶ X} (hab : a ≫ f = b ≫ f)
    (j : Z ⟶ T) [Nonempty Z] (hj : j ≫ a = j ≫ b) : a = b := by sorry
