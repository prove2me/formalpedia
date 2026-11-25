-- Prove2me | Theorems.Thm_GlobalTheory_IsLogBounded_comp_of_logWeight
-- name    : GlobalTheory.IsLogBounded.comp_of_logWeight
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:31.469005+00:00
-- url     : https://prove2.me/theorems/98b70f7f-f4fe-48d7-9a84-00cce1a4421b
-- title:
--   Is Log Bounded: comp of log Weight
-- statement:
--   The Is Log Bounded construction uses the comp of log Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L844-L851
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L844-L851

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
variable {κ κ' X X' m n : Type*} [TopologicalSpace X] [TopologicalSpace X']
variable [DecidableEq n] [DecidableEq m] {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
  {G G' : X → Matrix n n ℂ} {H : X → Matrix m m ℂ}
variable [Fintype n]
open GlobalTheory.IsLogBounded

theorem GlobalTheory.IsLogBounded.comp_of_logWeight (hG : IsLogBounded S w U G) {S' : Finset κ'}
    {w' : X' → κ' → ℂ} {U' : Set X'} {π : X' → X} (hπ : ContinuousOn π U') (hU : MapsTo π U' U)
    (hB : ∀ x ∈ U', x ∉ coordDivisor S' w' → π x ∉ coordDivisor S w)
    (hw : HasLogGrowth S' w' U' fun x => lwP₂ S (w (π x))) :
    IsLogBounded S' w' U' fun x => G (π x) := by sorry
