-- Prove2me | Theorems.Thm_GlobalTheory_WeilNoncomm_loc_comm
-- name    : GlobalTheory.WeilNoncomm.loc_comm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:10:47.740906+00:00
-- url     : https://prove2.me/theorems/9e67e950-40c8-4417-ac84-2eabdd30e1fd
-- title:
--   Weil Noncomm: loc comm
-- statement:
--   The Weil Noncomm construction uses the loc comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/NotWeilIsGrpPullbackNoncomm.lean#L131-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/NotWeilIsGrpPullbackNoncomm.lean#L131-L146

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NotWeilIsGrpPullbackNoncomm
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.WeilNoncomm
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1
variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

theorem GlobalTheory.WeilNoncomm.loc_comm {L : LB G.left} {k : ℤ} {T : Over S} (z : T.left) {θx θy : ThetaGrp G L k T} {c : Γ(T.left, ⊤)ˣ}
    (H : CommIsOf G L k θx θy c) (J : (T.left ⟶ G.left) → L.ι) (hJ : Good L z J) :
    loc G z θx 1 (J (1 : T ⟶ G).left) (J θx.pt.left) * loc G z θy θx.pt (J θx.pt.left) (J (θy.pt * θx.pt).left) =
      loc G z θy 1 (J (1 : T ⟶ G).left) (J θy.pt.left) * loc G z θx θy.pt (J θy.pt.left) (J (θx.pt * θy.pt).left) *
        gm ((lift (𝟙 T) (1 : T ⟶ G)).left ≫ (fst T G).left) z ⊤ c := by sorry
