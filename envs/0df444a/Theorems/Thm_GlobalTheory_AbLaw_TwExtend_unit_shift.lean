-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_TwExtend_unit_shift
-- name    : GlobalTheory.AbLaw.TwExtend.unit_shift
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T15:02:28.004246+00:00
-- url     : https://prove2.me/theorems/725caaaf-ed62-495a-a794-49d45bfcab17
-- title:
--   Tw Extend: unit shift
-- statement:
--   The Tw Extend construction uses the unit shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsTwExtendPowMul.lean#L60-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsTwExtendPowMul.lean#L60-L65

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

theorem GlobalTheory.AbLaw.TwExtend.unit_shift {R : Type} [CommRing R] (A B : Rˣ) (t d : ℤ) (k : ℕ) {u v : R}
    (h : u = (B ^ d).val * v) :
    (A * B ^ (t + k * d)).val * v ^ k = u ^ k * (A * B ^ t).val := by sorry
