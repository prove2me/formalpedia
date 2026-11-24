-- Prove2me | Theorems.Thm_GlobalTheory_dense_fibres_ext
-- name    : GlobalTheory.dense_fibres_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:16:22.55932+00:00
-- url     : https://prove2.me/theorems/b6976a18-c757-4783-b294-68e14fcc88e2
-- title:
--   Global Theory: dense fibres ext
-- statement:
--   The Global Theory construction uses the dense fibres ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLiftClosedImmersionOfDense.lean#L37-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLiftClosedImmersionOfDense.lean#L37-L53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLiftClosedImmersionOfDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.dense_fibres_ext :
    ∀ (X S : Scheme.{0}) [IsReduced X] (s : X ⟶ S) [Flat s] [LocallyOfFinitePresentation s]
      (Sg : Set S), Dense Sg → Dense (s ⁻¹' Sg) ∧
      (∀ (Y : Scheme.{0}) (t : Y ⟶ S) [IsSeparated t] (f g : X ⟶ Y), f ≫ t = s → g ≫ t = s →
        (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X),
          Set.range (x ≫ s) ⊆ Sg → x ≫ f = x ≫ g) → f = g) ∧
      (∀ (Y Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] (f : X ⟶ Y),
        (∀ x : X, s x ∈ Sg → f x ∈ Set.range i) → ∃ f' : X ⟶ Z, f' ≫ i = f) := by sorry
