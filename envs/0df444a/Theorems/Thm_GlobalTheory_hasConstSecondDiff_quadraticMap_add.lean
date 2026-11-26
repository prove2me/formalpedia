-- Prove2me | Theorems.Thm_GlobalTheory_hasConstSecondDiff_quadraticMap_add
-- name    : GlobalTheory.hasConstSecondDiff_quadraticMap_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:46:59.196167+00:00
-- url     : https://prove2.me/theorems/b28cd112-f1e1-4167-b019-b1c990488f4d
-- title:
--   Global Theory: has Const Second Diff quadratic Map add
-- statement:
--   The Global Theory construction uses the has Const Second Diff quadratic Map add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L113-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L113-L120

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
variable {X A : Type*} [AddCommGroup X] [AddCommGroup A]

theorem GlobalTheory.hasConstSecondDiff_quadraticMap_add (Q : QuadraticMap ℤ X A) (c : A) :
    HasConstSecondDiff fun x => Q x + c := by sorry
