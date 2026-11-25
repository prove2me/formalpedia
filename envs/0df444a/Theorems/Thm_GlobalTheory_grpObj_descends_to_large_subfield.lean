-- Prove2me | Theorems.Thm_GlobalTheory_grpObj_descends_to_large_subfield
-- name    : GlobalTheory.grpObj_descends_to_large_subfield
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:23:30.895608+00:00
-- url     : https://prove2.me/theorems/39314170-b976-4952-a690-d011acce85ca
-- title:
--   Global Theory: grp Obj descends to large subfield
-- statement:
--   The Global Theory construction uses the grp Obj descends to large subfield property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GrpObjDescendsToLargeSubfield.lean#L141-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GrpObjDescendsToLargeSubfield.lean#L141-L191

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MorphismsDescendToLargeSubfieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GrpObjDescendsToLargeSubfield
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
open GrpDescent

theorem GlobalTheory.grpObj_descends_to_large_subfield :
    ∀ (K : Type) [Field K] (K₀ : Subfield K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ A₀.left) [QuasiCompact A₀.hom] [QuasiSeparated A₀.hom] [LocallyOfFinitePresentation A₀.hom], IsPullback φ A.hom A₀.hom (spMap K₀.subtype) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (A₁ : Over (Sp K₁)) (φ₁ : A₁.left ⟶ A₀.left) (ψ : A.left ⟶ A₁.left), IsPullback φ₁ A₁.hom A₀.hom (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ A₁.hom = A.hom ≫ spMap K₁.subtype → ∃ _ : GrpObj A₁, IsGrpPullback A A₁ (spMap K₁.subtype) ψ := by sorry
