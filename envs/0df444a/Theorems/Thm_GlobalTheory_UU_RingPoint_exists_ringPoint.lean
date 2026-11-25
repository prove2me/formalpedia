-- Prove2me | Theorems.Thm_GlobalTheory_UU_RingPoint_exists_ringPoint
-- name    : GlobalTheory.UU.RingPoint.exists_ringPoint
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:25:35.690501+00:00
-- url     : https://prove2.me/theorems/1babc25c-2aea-4b76-bd75-e6237ead85f7
-- title:
--   Ring Point: exists ring Point
-- statement:
--   The Ring Point construction uses the exists ring Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsCompRedIff.lean#L28-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsCompRedIff.lean#L28-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompRedIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.RingPoint

theorem GlobalTheory.UU.RingPoint.exists_ringPoint {S : Scheme.{0}} (Y : Over S) [IsAffine Y.left] (D : Type) [CommRing D]
    (κ : Γ(Y.left, ⊤) →+* D) : ∃ (U : Over S) (y₀ : U ⟶ Y) (e : Γ(U.left, ⊤) ≃+* D), IsAffine U.left ∧
      (∀ b, e (y₀.left.appTop.hom b) = κ b) ∧
      ∀ (Z : Over S) (y : Z ⟶ Y) (θ : D →+* Γ(Z.left, ⊤)), (∀ b, θ (κ b) = y.left.appTop.hom b) →
        ∃ σ : Z ⟶ U, σ ≫ y₀ = y ∧ ∀ a, σ.left.appTop.hom a = θ (e a) := by sorry
