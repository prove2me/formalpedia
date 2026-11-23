-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_lift_of_etale
-- name    : GlobalTheory.existsUnique_lift_of_etale
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:35:55.470514+00:00
-- url     : https://prove2.me/theorems/1a3341a3-ddb6-41b7-b531-de961d75aeba
-- title:
--   Global Theory: exists Unique lift of etale
-- statement:
--   The Global Theory construction uses the exists Unique lift of etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L184-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L184-L217

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

theorem GlobalTheory.existsUnique_lift_of_etale {X S T₀ T : Scheme.{u}} (f : X ⟶ S) [Etale f]
    (i : T₀ ⟶ T) [IsClosedImmersion i] (hi : IsNilpotent i.ker)
    (g : T₀ ⟶ X) (h : T ⟶ S) (w : g ≫ f = i ≫ h) :
    ∃! l : T ⟶ X, i ≫ l = g ∧ l ≫ f = h := by sorry
