-- Prove2me | Theorems.Thm_GlobalTheory_WeilCube_weilIs_iff
-- name    : GlobalTheory.WeilCube.weilIs_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:47:14.686034+00:00
-- url     : https://prove2.me/theorems/f76bf5a0-bdaf-47fc-a95a-89ff5e25560a
-- title:
--   Weil Cube: weil Is iff
-- statement:
--   The Weil Cube construction uses the weil Is iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/WeilIsGrpPullbackIff.lean#L192-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/WeilIsGrpPullbackIff.lean#L192-L215

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
open GlobalTheory.WeilCube
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {Lr : RigLB A} (c : CubicalStr A Lr)

theorem GlobalTheory.WeilCube.weilIs_iff (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {k : ℕ} {T : Over S} {x y : T ⟶ A} (hx : x ^ k = 1)
    (hy : y ^ k = 1) {e₀ : Γ(T.left, ⊤)ˣ} (he : IsRatio c k x y e₀) (e : Γ(T.left, ⊤)ˣ) :
    WeilIs A Lr.L k x y e ↔ e = e₀ := by sorry
