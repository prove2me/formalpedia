-- Prove2me | Theorems.Thm_GlobalTheory_over_eq_of_preconnected_of_unramified
-- name    : GlobalTheory.over_eq_of_preconnected_of_unramified
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:49:34.459558+00:00
-- url     : https://prove2.me/theorems/798905ee-33f0-441c-bfc6-276f5eab2e78
-- title:
--   Global Theory: over eq of preconnected of unramified
-- statement:
--   The Global Theory construction uses the over eq of preconnected of unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L219-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L219-L224

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

theorem GlobalTheory.over_eq_of_preconnected_of_unramified {S Z : Scheme.{u}} {T X : Over S}
    [FormallyUnramified X.hom] [LocallyOfFiniteType X.hom] [IsSeparated X.hom]
    [PreconnectedSpace T.left] {a b : T ⟶ X}
    (j : Z ⟶ T.left) [Nonempty Z] (hj : j ≫ a.left = j ≫ b.left) : a = b := by sorry
