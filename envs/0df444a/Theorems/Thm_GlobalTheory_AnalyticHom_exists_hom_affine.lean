-- Prove2me | Theorems.Thm_GlobalTheory_AnalyticHom_exists_hom_affine
-- name    : GlobalTheory.AnalyticHom.exists_hom_affine
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:55:59.252424+00:00
-- url     : https://prove2.me/theorems/f2c95a18-fff6-4615-afd8-7c31e5dde5eb
-- title:
--   Analytic Hom: exists hom affine
-- statement:
--   The Analytic Hom construction uses the exists hom affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsHomOfLinearScalingHermForm.lean#L85-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsHomOfLinearScalingHermForm.lean#L85-L119

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsHomOfLinearScalingHermForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.AnalyticHom
open CubeValues SymmetricSemicharacter ComplexPoints AffinePointValues
variable {X Y : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X] {Z : Type}
  (ex : Z → (Sp ℂ ⟶ X)) (ey : Z → (Sp ℂ ⟶ Y))
  (hon : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ∃ z, ex z = x)
include hon

theorem GlobalTheory.AnalyticHom.exists_hom_affine {W : X.Opens} {D : Y.Opens} (hW : IsAffineOpen W) (hD : IsAffineOpen D)
    (hin : ∀ w, ⊤ ≤ ex w ⁻¹ᵁ W → ⊤ ≤ ey w ⁻¹ᵁ D)
    (hfn : ∀ f : Γ(Y, D), ∃ h : Γ(X, W), ∀ w, ⊤ ≤ ex w ⁻¹ᵁ W →
      valAt' (ex w) W h = valAt' (ey w) D f) :
    ∃ g : W.toScheme ⟶ Y, ∀ w (y : Sp ℂ ⟶ W.toScheme), y ≫ W.ι = ex w → y ≫ g = ey w := by sorry
