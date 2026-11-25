-- Prove2me | Theorems.Thm_GlobalTheory_HolTheta_normal_form
-- name    : GlobalTheory.HolTheta.normal_form
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T17:07:46.374892+00:00
-- url     : https://prove2.me/theorems/523e7c0b-87a0-5756-b632-ae604710306e
-- title:
--   Hol Theta: normal form
-- statement:
--   The Hol Theta construction uses the normal form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsThetaHolomorphic.lean#L42-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsThetaHolomorphic.lean#L42-L93

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasSumPolyDerivMulProdAddMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsThetaHolomorphic
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
open GlobalTheory GlobalTheory.HolTheta
open Matrix GlobalTheory.CanTh GlobalTheory.RiemannRel
variable {g : ℕ}
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
open Matrix
variable {g : ℕ}

theorem GlobalTheory.HolTheta.normal_form (G : Matrix (Fin g) (Fin g) ℂ) (e f : Fin g → Fin g → ℂ) (hG : G.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G z z).re)
    (hee : ∀ j k, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (e j) (e k)).im = 0) (hff : ∀ j k, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (f j) (f k)).im = 0)
    (hef : ∀ j k, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (e j) (f k)).im = -(1 : Matrix (Fin g) (Fin g) ℝ) j k)
    {A τ : Matrix (Fin g) (Fin g) ℂ} (hA : A = Matrix.of fun i j => e j i)
    (hτ : τ = A⁻¹ * Matrix.of fun i j => f j i) :
    IsUnit A.det ∧ τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧
      ∀ z w, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G z w = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (_root_.GlobalTheory.CanTh.imInv τ) (A⁻¹ *ᵥ z) (A⁻¹ *ᵥ w) := by sorry
