-- Prove2me | Theorems.Thm_GlobalTheory_IsoDesc_quot_invariant
-- name    : GlobalTheory.IsoDesc.quot_invariant
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:39:51.103577+00:00
-- url     : https://prove2.me/theorems/f049f313-a523-4b49-8450-566b6d855a7d
-- title:
--   Iso Desc: quot invariant
-- statement:
--   The Iso Desc construction uses the quot invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsCPMapDescends.lean#L383-L445
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsCPMapDescends.lean#L383-L445

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsCPMapDescends
import Theorems.Thm_GlobalTheory_UU_IsWt_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.IsoDesc
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] [Module.Free ℤ X] {G : Over S'} {B : Over S}
  [GrpObj G] [IsCommMonObj G] [ConnectedSpace G.left] [GrpObj B] [IsCommMonObj B] {Q : TQ G X} {P : CP G}
  {M' : CP Q.B} {M : CP B} {β : Q.B.left ⟶ B.left} {hβ : β ≫ B.hom = Q.B.hom ≫ f}

theorem GlobalTheory.IsoDesc.quot_invariant (mul : ∀ (T : Over S') (x y : T ⟶ Q.B), toBase hβ (x * y) = toBase hβ x * toBase hβ y)
    {hq : Q.q.left ≫ Q.B.hom = G.hom ≫ 𝟙 S'} {hw : (Q.q.left ≫ β) ≫ B.hom = G.hom ≫ f} {u w}
    (Hu : IsCPMap P M' (𝟙 S') Q.q.left hq u) (Hw : IsCPMap P M f (Q.q.left ≫ β) hw w) {s} (hs : IsQuot u w s)
    {Z : Over S'} (t : Z ⟶ splitTorus S' X) (g : Z ⟶ G) (z : Z.left) (j i)
    (hz : Q.q.left (g.left z) ∈ dom M'.L.L M.L.L β j i) :
    gm ((t ≫ Q.i) * g).left z _ (s j i) = gm g.left z _ (s j i) := by sorry
