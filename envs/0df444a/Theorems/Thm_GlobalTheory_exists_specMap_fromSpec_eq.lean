-- Prove2me | Theorems.Thm_GlobalTheory_exists_specMap_fromSpec_eq
-- name    : GlobalTheory.exists_specMap_fromSpec_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:41.611536+00:00
-- url     : https://prove2.me/theorems/1b50c88f-433f-4098-b50c-512684616e9b
-- title:
--   Global Theory: exists spec Map from Spec eq
-- statement:
--   The Global Theory construction uses the exists spec Map from Spec eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L285-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L285-L290

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

theorem GlobalTheory.exists_specMap_fromSpec_eq {X : Scheme.{u}} {R : CommRingCat.{u}} (g : Spec R ⟶ X)
    {V : X.Opens} (hV : IsAffineOpen V) (hg : Set.range g ⊆ V) :
    ∃ φ : Γ(X, V) ⟶ R, Spec.map φ ≫ hV.fromSpec = g := by sorry
