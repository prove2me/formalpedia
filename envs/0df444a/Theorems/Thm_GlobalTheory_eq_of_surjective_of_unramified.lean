-- Prove2me | Theorems.Thm_GlobalTheory_eq_of_surjective_of_unramified
-- name    : GlobalTheory.eq_of_surjective_of_unramified
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:17:43.76295+00:00
-- url     : https://prove2.me/theorems/5d6987bc-5b2e-42e2-9301-acfa84ea7fb6
-- title:
--   Global Theory: eq of surjective of unramified
-- statement:
--   The Global Theory construction uses the eq of surjective of unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L70-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L70-L74

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

theorem GlobalTheory.eq_of_surjective_of_unramified {X S T Z : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] {a b : T ⟶ X} (hab : a ≫ f = b ≫ f)
    (j : Z ⟶ T) [Surjective j] (hj : j ≫ a = j ≫ b) : a = b := by sorry
