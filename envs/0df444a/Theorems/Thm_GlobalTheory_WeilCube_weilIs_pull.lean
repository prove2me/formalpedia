-- Prove2me | Theorems.Thm_GlobalTheory_WeilCube_weilIs_pull
-- name    : GlobalTheory.WeilCube.weilIs_pull
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:20.704826+00:00
-- url     : https://prove2.me/theorems/b92c655f-bcd0-4ec1-8d89-ac6d596b97d6
-- title:
--   Weil Cube: weil Is pull
-- statement:
--   The Weil Cube construction uses the weil Is pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/WeilIsGrpPullbackIff.lean#L279-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/WeilIsGrpPullbackIff.lean#L279-L316

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
include c

theorem GlobalTheory.WeilCube.weilIs_pull (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {S₀ : Scheme.{0}} {G : Over S₀} [GrpObj G]
    {L₀ : LB G.left} (hL₀ : L₀.IsLB) {f : S ⟶ S₀} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
    (w : LB.Iso Lr.L (L₀.pull φ)) (hw : w.IsGen) {k : ℕ} {T : Over S} {T₀ : Over S₀} (τ : T.left ⟶ T₀.left)
    (hτ : τ ≫ T₀.hom = T.hom ≫ f) {x y : T ⟶ A} (hx : x ^ k = 1) (hy : y ^ k = 1) {x₀ y₀ : T₀ ⟶ G}
    (ex : τ ≫ x₀.left = x.left ≫ φ) (ey : τ ≫ y₀.left = y.left ≫ φ) {e₀ : Γ(T₀.left, ⊤)ˣ}
    (H : WeilIs G L₀ k x₀ y₀ e₀) : WeilIs A Lr.L k x y (Units.map τ.appTop.hom.toMonoidHom e₀) := by sorry
