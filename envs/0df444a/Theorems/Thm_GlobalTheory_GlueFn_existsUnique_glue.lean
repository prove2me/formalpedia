-- Prove2me | Theorems.Thm_GlobalTheory_GlueFn_existsUnique_glue
-- name    : GlobalTheory.GlueFn.existsUnique_glue
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:51.674121+00:00
-- url     : https://prove2.me/theorems/bc97d3f5-24d8-4421-9484-5dc339bc45ce
-- title:
--   Glue Fn: exists Unique glue
-- statement:
--   The Glue Fn construction uses the exists Unique glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueSectionOfLocallyRegular.lean#L46-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueSectionOfLocallyRegular.lean#L46-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EqZeroOfForallAlgHomComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSectionOfLocallyRegular
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.GlueFn

theorem GlobalTheory.GlueFn.existsUnique_glue {X : Over (Sp ℂ)} [IsReduced X.left] [LocallyOfFiniteType X.hom] {E : Type}
    (e : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (he : Function.Surjective e) (O : X.left.Opens) (ψ : E → ℂ)
    (h : ∀ z, ⊤ ≤ (e z).left ⁻¹ᵁ O → ∃ (O' : X.left.Opens) (a : Γ(X.left, O')), O' ≤ O ∧
      ⊤ ≤ (e z).left ⁻¹ᵁ O' ∧ ∀ z', ⊤ ≤ (e z').left ⁻¹ᵁ O' → valAt' (e z').left O' a = ψ z') :
    ∃! a : Γ(X.left, O), ∀ z, ⊤ ≤ (e z).left ⁻¹ᵁ O → valAt' (e z).left O a = ψ z := by sorry
