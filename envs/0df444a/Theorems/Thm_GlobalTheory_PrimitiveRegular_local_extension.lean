-- Prove2me | Theorems.Thm_GlobalTheory_PrimitiveRegular_local_extension
-- name    : GlobalTheory.PrimitiveRegular.local_extension
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T17:10:26.780934+00:00
-- url     : https://prove2.me/theorems/cbd051be-6a39-5b97-999c-0dba1c033418
-- title:
--   Primitive Regular: local extension
-- statement:
--   The Primitive Regular construction uses the local extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PrimitiveRegularOnSectionNonzeroLocus.lean#L77-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PrimitiveRegularOnSectionNonzeroLocus.lean#L77-L135

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

theorem GlobalTheory.PrimitiveRegular.local_extension (u : HolUnif A L g) (hL : L.IsLB) {I : Type} (O : I → A.left.Opens)
    (c : ∀ i i', Γ(A.left, O i ⊓ O i')) (h : I → (Fin g → ℂ) → ℂ) (hO : ⨆ i, O i = ⊤)
    (hh : ∀ i, DifferentiableOn ℂ (h i) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i})
    (hc : ∀ i i' z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (O i ⊓ O i') →
      valAt' (u.ex z).left (O i ⊓ O i') (c i i') = h i' z - h i z)
    (i : I) {n : ℕ} (σ : (lbPow L n).Sec) (hσ : Out.nonzeroLocus σ ≤ O i) {θ : (Fin g → ℂ) → ℂ}
    (hd : Differentiable ℂ θ) (hθ : u.IsFnPow n σ θ) (x : A.left) :
    ∃ (Q : A.left.Opens) (N : ℕ) (F : (Fin g → ℂ) → ℂ), x ∈ Q ∧
      DifferentiableOn ℂ F {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ Q} ∧
      ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ Q → θ z ≠ 0 → θ z ^ N * h i z = F z := by sorry
