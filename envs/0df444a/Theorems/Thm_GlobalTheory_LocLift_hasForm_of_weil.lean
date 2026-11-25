-- Prove2me | Theorems.Thm_GlobalTheory_LocLift_hasForm_of_weil
-- name    : GlobalTheory.LocLift.hasForm_of_weil
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:27:27.754862+00:00
-- url     : https://prove2.me/theorems/bf1a084c-5805-5398-aac9-b760b2295046
-- title:
--   Loc Lift: has Form of weil
-- statement:
--   The Loc Lift construction uses the has Form of weil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsHolLinearLift.lean#L121-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsHolLinearLift.lean#L121-L167

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearEquivLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitOnInjectiveOfCommRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolLinearLift
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
open Filter Topology
open GlobalTheory GlobalTheory.LocLift
noncomputable section
variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m : ℕ}

theorem GlobalTheory.LocLift.hasForm_of_weil (hT : ThetaUnifAV) (hB : Out.PolBaseChangeSt)
    (A : Out.PolAV X) (y₀ y : Sp ℂ ⟶ X) (hy : y = (𝟙_ (Over (Sp ℂ))).hom ≫ y₀)
    {e : (Fin g → ℂ) → (Over.mk y ⟶ A.A)} (he : IsExp y e) {r : ℝ} (hr : 0 < r)
    (hk : ∀ z, ‖z‖ < r → e z = 1 → z = 0)
    (hl : ∀ (n : ℕ) (x : (Fin n → ℂ) → (Over.mk y ⟶ A.A)), IsHolTo Set.univ (fun w => (x w).left) → e 0 = x 0 →
      ∃ ζ : (Fin n → ℂ) → (Fin g → ℂ), AnalyticAt ℂ ζ 0 ∧ ∀ᶠ w in 𝓝 0, e (ζ w) = x w)
    {La : Type} [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (P : La → (Fin g → ℂ)) (hP : ∀ a, e (P a) = 1)
    (hw : ∀ (k : ℕ) (a a₂ : La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a a₂ : ℂ) / k) →
      Out.WeilIs A.A A.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (unitOn c)) : HasForm EF P := by sorry
