-- Prove2me | Theorems.Thm_GlobalTheory_HasLogGrowth_comp_of_logWeight
-- name    : GlobalTheory.HasLogGrowth.comp_of_logWeight
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:55:01.345382+00:00
-- url     : https://prove2.me/theorems/b5bae8dc-e7f7-4fb1-9df9-74ef708f32bd
-- title:
--   Has Log Growth: comp of log Weight
-- statement:
--   The Has Log Growth construction uses the comp of log Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L175-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L175-L184

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology
open GlobalTheory
variable {κ κ' X X' E F : Type*} [TopologicalSpace X] [TopologicalSpace X']
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
open GlobalTheory.HasLogGrowth

theorem GlobalTheory.HasLogGrowth.comp_of_logWeight {f : X → E} (hf : HasLogGrowth S w U f) {S' : Finset κ'}
    {w' : X' → κ' → ℂ} {U' : Set X'} {π : X' → X} (hπ : ContinuousOn π U') (hU : MapsTo π U' U)
    (hB : ∀ x ∈ U', x ∉ coordDivisor S' w' → π x ∉ coordDivisor S w)
    (hw : HasLogGrowth S' w' U' fun x => GlobalTheory.lwP₂ S (w (π x))) :
    HasLogGrowth S' w' U' fun x => f (π x) := by sorry
