-- Prove2me | Theorems.Thm_GlobalTheory_SiegelPeriod_exists_siegel_form
-- name    : GlobalTheory.SiegelPeriod.exists_siegel_form
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:12:19.872384+00:00
-- url     : https://prove2.me/theorems/46117343-ec6e-471d-933b-a6f25edf7821
-- title:
--   Siegel Period: exists siegel form
-- statement:
--   The Siegel Period construction uses the exists siegel form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSiegelForm.lean#L15-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSiegelForm.lean#L15-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSiegelForm
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
open GlobalTheory GlobalTheory.SiegelPeriod
open GlobalTheory.SiegelNormalForm Matrix

theorem GlobalTheory.SiegelPeriod.exists_siegel_form : ∀ (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ a b, EF (bas a) (bas b) = omegaStd a b) → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → ∃ h τ : Matrix (Fin g) (Fin g) ℂ, IsUnit h ∧ h⁻¹ = (Matrix.of fun i j => Q (bas (Pi.single (.inr j) 1)) i) ∧ τ = h * (Matrix.of fun i j => Q (bas (Pi.single (.inl j) 1)) i) ∧ τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ (∀ z w, hermForm Hm z w = hermForm (((τ.map Complex.im)⁻¹).map Complex.ofReal) (h.mulVec z) (h.mulVec w)) ∧ ∀ a, h.mulVec (Q (bas a)) = τ.mulVec (fun i => (a (.inl i) : ℂ)) + fun i => (a (.inr i) : ℂ) := by sorry
