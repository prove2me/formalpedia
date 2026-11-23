-- Prove2me | Theorems.Thm_GlobalTheory_weilIs_iso_iff
-- name    : GlobalTheory.weilIs_iso_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:29.782798+00:00
-- url     : https://prove2.me/theorems/9ece401a-510b-416c-b0df-7ff2ab707700
-- title:
--   Global Theory: weil Is iso iff
-- statement:
--   The Global Theory construction uses the weil Is iso iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/WeilIsGrpPullbackIff.lean#L352-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/WeilIsGrpPullbackIff.lean#L352-L357

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
open WeilCube

theorem GlobalTheory.weilIs_iso_iff (hG : GlobalFnsSt) (hC : CubeSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P' P : PolAV S)
    (θ : P'.A ≅ P.A) [IsMonHom θ.hom] (w : LB.Iso P'.L (P.L.pull θ.hom.left)) (hw : w.IsGen) {T : Over S} (k : ℕ)
    (x y : T ⟶ P'.A) (hx : x ^ k = 1) (hy : y ^ k = 1) (e : Γ(T.left, ⊤)ˣ) :
    WeilIs P.A P.L k (x ≫ θ.hom) (y ≫ θ.hom) e ↔ WeilIs P'.A P'.L k x y e := by sorry
