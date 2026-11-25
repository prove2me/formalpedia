-- Prove2me | Theorems.Thm_GlobalTheory_PrimCocycle_val_mul_eq
-- name    : GlobalTheory.PrimCocycle.val_mul_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:16.049337+00:00
-- url     : https://prove2.me/theorems/83fcedd9-65ff-4a6d-91a1-70b30bb78526
-- title:
--   Prim Cocycle: val mul eq
-- statement:
--   The Prim Cocycle construction uses the val mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/PrimitiveCocycle.lean#L64-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/PrimitiveCocycle.lean#L64-L95

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_PrimitiveCocycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PrimCocycle
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]

theorem GlobalTheory.PrimCocycle.val_mul_eq (hG : GlobalFnsSt) (hB : IsAbelianScheme B) {L : LB B.left} (hL : L.IsLB)
    (u : LB.Gen (LB.LinComb L (lamφ B) lamε)) (hu : u.IsGen)
    (e : 𝟙_ (Over S) ⟶ G3 B) (a b c d a' b' c' d' : G3 B ⟶ B)
    (hF : ∀ (V : Type) [CommGroup V] (k : (G3 B ⟶ B) → V),
      (k (a' * b') * (k a')⁻¹ * (k b')⁻¹ * k 1) * (k (c' * d') * (k c')⁻¹ * (k d')⁻¹ * k 1) =
      (k (a * b) * (k a)⁻¹ * (k b)⁻¹ * k 1) * (k (c * d) * (k c)⁻¹ * (k d)⁻¹ * k 1))
    (ha : e ≫ a = 1) (hb : e ≫ b = 1) (hc : e ≫ c = 1) (hd : e ≫ d = 1)
    (ha' : e ≫ a' = 1) (hb' : e ≫ b' = 1) (hc' : e ≫ c' = 1) (hd' : e ≫ d' = 1)
    {T : Over S} (ρ : T ⟶ G3 B) {z : T.left} {J} (hJ : Good L z J) :
    val₂ u z J (ρ ≫ a) (ρ ≫ b) * val₂ u z J (ρ ≫ c) (ρ ≫ d) =
      val₂ u z J (ρ ≫ a') (ρ ≫ b') * val₂ u z J (ρ ≫ c') (ρ ≫ d') := by sorry
