-- Prove2me | Theorems.Thm_GlobalTheory_T_primitive_regular_on_section_nonzeroLocus
-- name    : GlobalTheory.T.primitive_regular_on_section_nonzeroLocus
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T17:25:26.81414+00:00
-- url     : https://prove2.me/theorems/ed8a91de-f0df-4c74-b51e-b5c4c7edfd01
-- title:
--   T: primitive regular on section nonzero Locus
-- statement:
--   The T construction uses the primitive regular on section nonzero Locus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PrimitiveRegularOnSectionNonzeroLocusStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PrimitiveRegularOnSectionNonzeroLocusStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PrimitiveRegularOnSectionNonzeroLocus
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PrimitiveRegularOnSectionNonzeroLocusStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.primitive_regular_on_section_nonzeroLocus : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (I : Type) (O : I → P₀.A.left.Opens) (c : ∀ i i', Γ(P₀.A.left, O i ⊓ O i')) (h : I → (Fin P₀.g → ℂ) → ℂ), ⨆ i, O i = ⊤ → (∀ i, DifferentiableOn ℂ (h i) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i} ∧ ∀ (l : u.Λ) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i → h i (z + l) = h i z) → (∀ i i' z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (O i ⊓ O i') → valAt' (u.ex z).left (O i ⊓ O i') (c i i') = h i' z - h i z) → ∀ i (n : ℕ) (σ : (lbPow P₀.L n).Sec), Out.nonzeroLocus σ ≤ O i → ∃ a : Γ(P₀.A.left, Out.nonzeroLocus σ), ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ Out.nonzeroLocus σ → valAt' (u.ex z).left (Out.nonzeroLocus σ) a = h i z := by sorry
