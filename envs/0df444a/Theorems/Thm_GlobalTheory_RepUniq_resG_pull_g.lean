-- Prove2me | Theorems.Thm_GlobalTheory_RepUniq_resG_pull_g
-- name    : GlobalTheory.RepUniq.resG_pull_g
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:34:23.116796+00:00
-- url     : https://prove2.me/theorems/01fa9f8a-0052-4aa9-8df1-b8ccc043e566
-- title:
--   Rep Uniq: res G pull g
-- statement:
--   The Rep Uniq construction uses the res G pull g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsoOfProjectiveCoordinateRepresentation.lean#L134-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsoOfProjectiveCoordinateRepresentation.lean#L134-L140

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsoOfProjectiveCoordinateRepresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.RepUniq
open TopologicalSpace GlobalTheory.Cartier GlobalTheory.ProjSpace
variable {σ : Type} {T T' X X' X'' : Scheme.{0}}
variable {M : LB X} {th : σ → M.Sec} {M' : LB X'} {th' : σ → M'.Sec} {M'' : LB X''} {th'' : σ → M''.Sec}
  {x : T ⟶ X} {x' : T ⟶ X'} {x'' : T ⟶ X''}

theorem GlobalTheory.RepUniq.resG_pull_g (x : T ⟶ X) (j k : PUnit → M.ι) {W : T.Opens} (hj : W ≤ (M.pull x).U j)
    (hk : W ≤ (M.pull x).U k) :
    resG T (le_inf hj hk) ((M.pull x).g j k).val =
      (x.appLE (M.U (j ⟨⟩) ⊓ M.U (k ⟨⟩)) W
        (le_inf (hj.trans (pull_U M x j).le) (hk.trans (pull_U M x k).le))).hom (M.g (j ⟨⟩) (k ⟨⟩)).val := by sorry
