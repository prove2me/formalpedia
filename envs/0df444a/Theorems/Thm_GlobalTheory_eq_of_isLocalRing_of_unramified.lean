-- Prove2me | Theorems.Thm_GlobalTheory_eq_of_isLocalRing_of_unramified
-- name    : GlobalTheory.eq_of_isLocalRing_of_unramified
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:27.023912+00:00
-- url     : https://prove2.me/theorems/5ebce833-8ab0-4c75-82e3-cd11f0320a0e
-- title:
--   Global Theory: eq of is Local Ring of unramified
-- statement:
--   The Global Theory construction uses the eq of is Local Ring of unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L93-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L93-L102

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

theorem GlobalTheory.eq_of_isLocalRing_of_unramified {X S Z : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] {R : CommRingCat.{u}} [IsLocalRing R]
    {a b : Spec R ⟶ X} (hab : a ≫ f = b ≫ f)
    (j : Z ⟶ Spec R) (hz : IsLocalRing.closedPoint R ∈ Set.range j) (hj : j ≫ a = j ≫ b) :
    a = b := by sorry
