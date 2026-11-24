-- Prove2me | Theorems.Thm_GlobalTheory_TorsorUnit_exists_coaction
-- name    : GlobalTheory.TorsorUnit.exists_coaction
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:26.920082+00:00
-- url     : https://prove2.me/theorems/cf93e412-c334-4734-aaab-21173869d8a9
-- title:
--   Torsor Unit: exists coaction
-- statement:
--   The Torsor Unit construction uses the exists coaction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLocalUnitOfWeight.lean#L280-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLocalUnitOfWeight.lean#L280-L320

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorsorUnit
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
  {q : G ⟶ B} {i : splitTorus S X ⟶ G}
open SplitTorusPoints

theorem GlobalTheory.TorsorUnit.exists_coaction [IsMonHom q] (hi : IsPullback i (toUnit _) q η[B]) {V : B.left.Opens}
    (hU : IsAffineOpen (q.left ⁻¹ᵁ V)) :
    ∃ ρ : Γ(G.left, q.left ⁻¹ᵁ V) →+* AddMonoidAlgebra Γ(G.left, q.left ⁻¹ᵁ V) X,
      ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (θ), g.left = pt hU θ →
        ((t ≫ i) * g).left = pt hU ((ev θ (toHom t)).comp ρ) := by sorry
