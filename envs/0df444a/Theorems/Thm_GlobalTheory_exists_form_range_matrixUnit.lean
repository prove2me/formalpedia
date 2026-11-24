-- Prove2me | Theorems.Thm_GlobalTheory_exists_form_range_matrixUnit
-- name    : GlobalTheory.exists_form_range_matrixUnit
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:32:43.670241+00:00
-- url     : https://prove2.me/theorems/9de7f4d0-e8fa-4f96-a82c-5c108095d57a
-- title:
--   Global Theory: exists form range matrix Unit
-- statement:
--   The Global Theory construction uses the exists form range matrix Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsEquivPiRangeOfMatrixUnits.lean#L88-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsEquivPiRangeOfMatrixUnits.lean#L88-L141

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_UnimodularSymplecticCoordinatesAndLatticeRank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSiegelForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsEquivPiRangeOfMatrixUnits
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
open GlobalTheory

theorem GlobalTheory.exists_form_range_matrixUnit {La : Type} [AddCommGroup La] (G : Matrix (Fin 8) (Fin 8) ℤ)
    (EF : LinearMap.BilinForm ℤ La) (r : Matrix (Fin 8) (Fin 8) ℤ →+* Module.End ℤ La)
    (hG : G 0 0 ≠ 0) (hdet : G.det = 1) (hb : Function.Bijective EF) (halt : ∀ x, EF x x = 0)
    (hadj : ∀ a a', a.transpose * G = G * a' → ∀ x y, EF (r a x) y = EF x (r a' y)) :
    ∃ (φ : La ≃ₗ[ℤ] (Fin 8 → LinearMap.range (r (Matrix.single 0 0 1))))
      (E : LinearMap.BilinForm ℤ (LinearMap.range (r (Matrix.single 0 0 1)))),
      (∀ x u, (φ x u : La) = r (Matrix.single 0 u 1) x) ∧ Function.Bijective E ∧ (∀ x, E x x = 0) ∧
      (∀ x y, EF x y = ∑ u, ∑ v, G u v * E (φ x u) (φ y v)) ∧
      ∀ x y : LinearMap.range (r (Matrix.single 0 0 1)), EF x y = G 0 0 * E x y := by sorry
