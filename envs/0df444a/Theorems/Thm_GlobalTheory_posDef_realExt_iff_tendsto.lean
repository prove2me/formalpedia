-- Prove2me | Theorems.Thm_GlobalTheory_posDef_realExt_iff_tendsto
-- name    : GlobalTheory.posDef_realExt_iff_tendsto
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:49:25.193839+00:00
-- url     : https://prove2.me/theorems/95ccb9ff-f58d-5528-97e0-d69f0fc1b566
-- title:
--   Global Theory: pos Def real Ext iff tendsto
-- statement:
--   The Global Theory construction uses the pos Def real Ext iff tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L354-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L354-L356

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

theorem GlobalTheory.posDef_realExt_iff_tendsto [Module.Free ℤ X] [Module.Finite ℤ X]
    (Q : QuadraticMap ℤ X ℝ) : (realExt Q).PosDef ↔ Tendsto Q cofinite atTop := by sorry
