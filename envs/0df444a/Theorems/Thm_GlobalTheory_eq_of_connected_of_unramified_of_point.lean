-- Prove2me | Theorems.Thm_GlobalTheory_eq_of_connected_of_unramified_of_point
-- name    : GlobalTheory.eq_of_connected_of_unramified_of_point
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:17:25.014951+00:00
-- url     : https://prove2.me/theorems/5c35e890-fc41-459c-9c9a-87fbf879127b
-- title:
--   Global Theory: eq of connected of unramified of point
-- statement:
--   The Global Theory construction uses the eq of connected of unramified of point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L87-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L87-L91

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

theorem GlobalTheory.eq_of_connected_of_unramified_of_point {X S T : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] [IsSeparated f] [ConnectedSpace T]
    {a b : T ⟶ X} (hab : a ≫ f = b ≫ f)
    {k : Type u} [Field k] (j : Spec (.of k) ⟶ T) (hj : j ≫ a = j ≫ b) : a = b := by sorry
