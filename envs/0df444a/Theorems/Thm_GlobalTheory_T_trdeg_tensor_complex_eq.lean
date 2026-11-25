-- Prove2me | Theorems.Thm_GlobalTheory_T_trdeg_tensor_complex_eq
-- name    : GlobalTheory.T.trdeg_tensor_complex_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:39:51.020806+00:00
-- url     : https://prove2.me/theorems/fdf193a7-f518-531d-88f6-6223f627dfed
-- title:
--   T: trdeg tensor complex eq
-- statement:
--   The T construction uses the trdeg tensor complex eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TrdegComplexBaseChangeEqStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TrdegComplexBaseChangeEqStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TrdegComplexBaseChangeEq
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TrdegComplexBaseChangeEqStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.trdeg_tensor_complex_eq : ∀ {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ'] [IsDomain (K ⊗[ℂ] κ')], Algebra.trdeg K (K ⊗[ℂ] κ') = Algebra.trdeg ℂ κ' := by sorry
