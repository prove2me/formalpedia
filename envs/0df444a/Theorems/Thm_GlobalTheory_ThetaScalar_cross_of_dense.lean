-- Prove2me | Theorems.Thm_GlobalTheory_ThetaScalar_cross_of_dense
-- name    : GlobalTheory.ThetaScalar.cross_of_dense
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:08:43.750346+00:00
-- url     : https://prove2.me/theorems/db1a7232-51a7-447d-9a73-40bf461328b6
-- title:
--   Theta Scalar: cross of dense
-- statement:
--   The Theta Scalar construction uses the cross of dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TorsionEqOneOfTranslationKeepsRatios.lean#L313-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TorsionEqOneOfTranslationKeepsRatios.lean#L313-L339

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaScalar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
  ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S}

theorem GlobalTheory.ThetaScalar.cross_of_dense (hL : L.IsLB) (θ : ThetaGrp A L k T) {I : Type*} {Z : Scheme.{0}} (z : Z)
    (r : I → (Z ⟶ (T ⊗ A).left)) (J₀ : (Z ⟶ A.left) → L.ι) (hJ₀ : Good L z J₀)
    (dense : ∀ u : LB.Sec (LPow A L (k + k) T), (∀ i, secVal u (r i) z J₀ = 0) → ∀ j, u.f j = 0)
    (ratio : ∀ s t : LB.Sec (LPow A L k T), ∀ i,
      secVal s (r i ≫ (translT A θ.pt).left) z J₀ * secVal t (r i) z J₀ =
        secVal t (r i ≫ (translT A θ.pt).left) z J₀ * secVal s (r i) z J₀)
    (s s' t t' : LB.Sec (LPow A L k T)) (hs : ActVal θ s s') (ht : ActVal θ t t') (y : (T ⊗ A).left)
    (J : ((T ⊗ A).left ⟶ A.left) → L.ι) (hJ : Good L y J) :
    secVal s' (𝟙 _) y J * secVal t (𝟙 _) y J = secVal t' (𝟙 _) y J * secVal s (𝟙 _) y J := by sorry
