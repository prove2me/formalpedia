-- Prove2me | Theorems.Thm_GlobalTheory_UU_exists_isCPMap
-- name    : GlobalTheory.UU.exists_isCPMap
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:43:20.143245+00:00
-- url     : https://prove2.me/theorems/89c518b8-e881-4fa2-afac-4d419433c626
-- title:
--   UU: exists is CPMap
-- statement:
--   The UU construction uses the exists is CPMap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/PointEqOfSubsingleton.lean#L467-L590
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/PointEqOfSubsingleton.lean#L467-L590

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm

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
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S S' : Scheme.{0}}
attribute [instance] TQ.grp TQ.comm
variable {S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']
  {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}

theorem GlobalTheory.UU.exists_isCPMap (P : CP G)
    (mul : ∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y)
    (L' : LB G'.left) (hL' : L'.IsLB) (w : LB.Iso L' (P.L.L.pull F)) (hg : w.IsGen) :
    ∃ (rig : LB.Gen (L'.pull (eSec G'))) (hr : rig.IsGen) (c : CubicalStr G' ⟨L', rig, hL', hr⟩) (s : _) (h₁ : _)
      (h₂ : _) (h₃ : _), IsCPMap ⟨⟨L', rig, hL', hr⟩, c, s, h₁, h₂, h₃⟩ P f F hw w := by sorry
