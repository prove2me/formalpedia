-- Prove2me | Theorems.Thm_GlobalTheory_EvenCubicNorm_prodPow_single
-- name    : GlobalTheory.EvenCubicNorm.prodPow_single
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:05:21.082807+00:00
-- url     : https://prove2.me/theorems/bd421738-6029-4267-aa4e-479714ac9bf0
-- title:
--   Even Cubic Norm: prod Pow single
-- statement:
--   The Even Cubic Norm construction uses the prod Pow single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEvenCubicUnitMultipleFractionRing.lean#L66-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEvenCubicUnitMultipleFractionRing.lean#L66-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEvenCubicUnitMultipleFractionRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.EvenCubicNorm
open Finset
variable {M : Type*} [CommGroup M] {ι : Type*} [Fintype ι]

theorem GlobalTheory.EvenCubicNorm.prodPow_single [DecidableEq ι] (z : ι → ι → M) (k l : ι) :
    prodPow z (fun i j => if i = k ∧ j = l then 1 else 0) = z k l := by sorry
