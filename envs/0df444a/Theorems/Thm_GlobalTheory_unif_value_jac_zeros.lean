-- Prove2me | Theorems.Thm_GlobalTheory_unif_value_jac_zeros
-- name    : GlobalTheory.unif_value_jac_zeros
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T17:31:28.91766+00:00
-- url     : https://prove2.me/theorems/1ba4067d-b5d6-5e1e-a6d5-42428449f242
-- title:
--   Global Theory: unif value jac zeros
-- statement:
--   The Global Theory construction uses the unif value jac zeros property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/UnifValueJacZeros.lean#L103-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/UnifValueJacZeros.lean#L103-L153

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_LevBasis
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KaRuleK
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_UnifValueJacZeros
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
noncomputable section
open GlobalTheory
open UnifJac

theorem GlobalTheory.unif_value_jac_zeros : ThetaUnifAV → ∀ (g : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (n : ℕ) (s : Fin x.P.g → RR x n) (F : Fin x.P.g → (Fin g → ℂ) → ℂ) (z : Fin g → ℂ) (c : x.P.L.ι), Wit x h u τ a b → (∀ i, Differentiable ℂ (F i) ∧ FnPw x u (s i) (F i)) → ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U c → (∀ i, valT (T := ℂ) (u.ex z).left (x.P.L.U c) ((s i).f c) = F i z * u.fr c z ^ n) ∧ ((∀ i, F i z = 0) → jac x s (u.ex z) c = u.fr c z ^ (g * n) * (Matrix.of fun i k : Fin x.P.g => (2 * Real.pi * Complex.I)⁻¹ * fderiv ℂ (F i) z (Pi.single (k.cast h) 1)).det) ∧ ∀ (d : ℕ) (zs : Fin d → Fin g → ℂ), (∀ y, (∀ i, F i y = 0) → ∃ a, ∃ e ∈ u.Λ, y = zs a + e) → ∀ y : x.P.A.left, (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ a, ∃ p : Sp ℂ, (u.ex (zs a)).left p = y := by sorry
