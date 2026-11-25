-- Prove2me | Theorems.Thm_GlobalTheory_exists_quotient_by_finite_group_of_points
-- name    : GlobalTheory.exists_quotient_by_finite_group_of_points
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:51:45.211365+00:00
-- url     : https://prove2.me/theorems/765f0e4f-43ee-585c-8c09-44702182766b
-- title:
--   Global Theory: exists quotient by finite group of points
-- statement:
--   The Global Theory construction uses the exists quotient by finite group of points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsQuotientByFiniteGroupOfPoints.lean#L233-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsQuotientByFiniteGroupOfPoints.lean#L233-L266

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsQuotientByFiniteGroupOfPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory
open PointQuot

theorem GlobalTheory.exists_quotient_by_finite_group_of_points :
    Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] (P : Out.PolAV (Sp k)) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ P.A)), Finite C → ∃ (B : Over (Sp k)) (_ : GrpObj B) (ψ : P.A ⟶ B), IsAbelianScheme B ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over (Sp k)) ⟶ P.A, x ≫ ψ = 1 ↔ x ∈ C) ∧ ∀ (Y : Over (Sp k)) (f : P.A ⟶ Y), (∀ x ∈ C, ((toUnit P.A ≫ x) * 𝟙 P.A) ≫ f = f) → ∃! f' : B ⟶ Y, ψ ≫ f' = f := by sorry
