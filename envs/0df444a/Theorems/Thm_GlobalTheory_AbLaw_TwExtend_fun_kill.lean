-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_TwExtend_fun_kill
-- name    : GlobalTheory.AbLaw.TwExtend.fun_kill
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:01:36.682066+00:00
-- url     : https://prove2.me/theorems/56bc3827-28e2-4135-a8db-aaead93eb0e3
-- title:
--   Tw Extend: fun kill
-- statement:
--   The Tw Extend construction uses the fun kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsTwExtendPowMul.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsTwExtendPowMul.lean#L34-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsTwExtendPowMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.TwExtend
variable {Y : Scheme.{0}}

theorem GlobalTheory.AbLaw.TwExtend.fun_kill {W O : Y.Opens} (hW : IsCompact (W : Set Y)) (f x : Γ(Y, W))
    (hO : Y.basicOpen f = O) (h : O ≤ W) (hx : rs Y h x = 0) : ∃ n : ℕ, f ^ n * x = 0 := by sorry
