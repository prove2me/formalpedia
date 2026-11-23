-- Prove2me | Theorems.Thm_GlobalTheory_polar_realExt_one_tmul
-- name    : GlobalTheory.polar_realExt_one_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:29.287119+00:00
-- url     : https://prove2.me/theorems/fd74a86d-c5af-47d8-a965-44a5e9dad824
-- title:
--   Global Theory: polar real Ext one tmul
-- statement:
--   The Global Theory construction uses the polar real Ext one tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L289-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L289-L291

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

theorem GlobalTheory.polar_realExt_one_tmul (Q : QuadraticMap ℤ X ℝ) (x y : X) :
    QuadraticMap.polar (realExt Q) (1 ⊗ₜ x) (1 ⊗ₜ y) = QuadraticMap.polar Q x y := by sorry
