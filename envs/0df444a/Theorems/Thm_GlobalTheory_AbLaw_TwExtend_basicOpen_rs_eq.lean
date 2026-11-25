-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_TwExtend_basicOpen_rs_eq
-- name    : GlobalTheory.AbLaw.TwExtend.basicOpen_rs_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:14:04.934835+00:00
-- url     : https://prove2.me/theorems/a5534c6b-2acc-56b8-aad7-d7db29db419c
-- title:
--   Tw Extend: basic Open rs eq
-- statement:
--   The Tw Extend construction uses the basic Open rs eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsTwExtendPowMul.lean#L15-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsTwExtendPowMul.lean#L15-L27

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

theorem GlobalTheory.AbLaw.TwExtend.basicOpen_rs_eq {L : LB Y} (s : LB.Sec L) (k : L.ι) {W : Y.Opens} (h : W ≤ L.U k) :
    Y.basicOpen (rs Y h (s.f k)) = nonzeroLocus s ⊓ W := by sorry
