-- Prove2me | Theorems.Thm_GlobalTheory_HasConstSecondDiff_posDef_realExt
-- name    : GlobalTheory.HasConstSecondDiff.posDef_realExt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:01:53.32157+00:00
-- url     : https://prove2.me/theorems/10e7ff3f-51fe-47a1-bbff-7f375b703abe
-- title:
--   Has Const Second Diff: pos Def real Ext
-- statement:
--   The Has Const Second Diff construction uses the pos Def real Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L388-L391
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L388-L391

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module TensorProduct
open GlobalTheory
variable {X : Type*} [AddCommGroup X]

theorem GlobalTheory.HasConstSecondDiff.posDef_realExt [Module.Finite ℤ X] {f : X → ℝ}
    (h : HasConstSecondDiff f) (he : ∀ x, f (-x) = f x) (ht : Tendsto f cofinite atTop) :
    (realExt (h.quadraticMap he)).PosDef := by sorry
