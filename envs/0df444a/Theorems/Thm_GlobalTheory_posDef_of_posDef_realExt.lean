-- Prove2me | Theorems.Thm_GlobalTheory_posDef_of_posDef_realExt
-- name    : GlobalTheory.posDef_of_posDef_realExt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:42.855014+00:00
-- url     : https://prove2.me/theorems/aa04f6f1-7b6e-4129-87f3-2c2612a48385
-- title:
--   Global Theory: pos Def of pos Def real Ext
-- statement:
--   The Global Theory construction uses the pos Def of pos Def real Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L379-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L379-L386

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

theorem GlobalTheory.posDef_of_posDef_realExt [Module.Free ℤ X] [Module.Finite ℤ X]
    {Q : QuadraticMap ℤ X ℝ} (hQ : (realExt Q).PosDef) : Q.PosDef := by sorry
