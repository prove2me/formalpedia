-- Prove2me | Theorems.Thm_GlobalTheory_PrimitiveRegular_entire_extension
-- name    : GlobalTheory.PrimitiveRegular.entire_extension
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T17:07:59.795891+00:00
-- url     : https://prove2.me/theorems/5cb4d3fa-358a-46c1-bfcd-e8a07716aed3
-- title:
--   Primitive Regular: entire extension
-- statement:
--   The Primitive Regular construction uses the entire extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PrimitiveRegularOnSectionNonzeroLocus.lean#L142-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PrimitiveRegularOnSectionNonzeroLocus.lean#L142-L163

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowThetaFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowEqThetaLevelChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSectionOfLocallyRegular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PrimitiveRegularOnSectionNonzeroLocus
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.PrimitiveRegular
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem GlobalTheory.PrimitiveRegular.entire_extension (u : HolUnif A L g) [CompactSpace A.left] (f θ : (Fin g → ℂ) → ℂ)
    (hd : Differentiable ℂ θ)
    (hloc : ∀ x : A.left, ∃ (Q : A.left.Opens) (N : ℕ) (F : (Fin g → ℂ) → ℂ), x ∈ Q ∧
      DifferentiableOn ℂ F {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ Q} ∧
      ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ Q → θ z ≠ 0 → θ z ^ N * f z = F z) :
    ∃ M : ℕ, 0 < M ∧ Differentiable ℂ fun z => θ z ^ M * f z := by sorry
