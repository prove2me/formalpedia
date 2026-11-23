-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_MulN_isPullback_baseChange
-- name    : GlobalTheory.AbLaw.MulN.isPullback_baseChange
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:08:27.360084+00:00
-- url     : https://prove2.me/theorems/b552da2d-1279-4033-847d-2614cf1b5c44
-- title:
--   Mul N: is Pullback base Change
-- statement:
--   The Mul N construction uses the is Pullback base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MulAFiniteFlatSurjectiveEtale.lean#L25-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MulAFiniteFlatSurjectiveEtale.lean#L25-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulAFiniteFlatSurjectiveEtale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.MulN

theorem GlobalTheory.AbLaw.MulN.isPullback_baseChange {S T : Scheme.{0}} (t : T ⟶ S) {X Y : Over S} (f : X ⟶ Y) :
    IsPullback (pullback.fst X.hom t) ((Over.pullback t).map f).left f.left
      (pullback.fst Y.hom t) := by sorry
