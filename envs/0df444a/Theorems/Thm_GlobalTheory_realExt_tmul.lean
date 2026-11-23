-- Prove2me | Theorems.Thm_GlobalTheory_realExt_tmul
-- name    : GlobalTheory.realExt_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:57:49.505102+00:00
-- url     : https://prove2.me/theorems/b9818356-d2b4-4c92-94ad-069e9b15940f
-- title:
--   Global Theory: real Ext tmul
-- statement:
--   The Global Theory construction uses the real Ext tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L276-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L276-L281

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

theorem GlobalTheory.realExt_tmul (Q : QuadraticMap ℤ X ℝ) (s : ℝ) (x : X) :
    realExt Q (s ⊗ₜ x) = s * s * Q x := by sorry
