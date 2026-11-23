-- Prove2me | Theorems.Thm_GlobalTheory_bijective_restrictPoints_of_existsUnique
-- name    : GlobalTheory.bijective_restrictPoints_of_existsUnique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:25.507639+00:00
-- url     : https://prove2.me/theorems/013bef05-c1e8-46fc-a815-3dc67a6eb946
-- title:
--   Global Theory: bijective restrict Points of exists Unique
-- statement:
--   The Global Theory construction uses the bijective restrict Points of exists Unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L346-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L346-L353

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

theorem GlobalTheory.bijective_restrictPoints_of_existsUnique {X S T₀ T : Scheme.{u}} (f : X ⟶ S) (h : T ⟶ S)
    (i : T₀ ⟶ T)
    (H : ∀ g : T₀ ⟶ X, g ≫ f = i ≫ h → ∃! l : T ⟶ X, i ≫ l = g ∧ l ≫ f = h) :
    Function.Bijective (restrictPoints f h i) := by sorry
