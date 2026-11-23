-- Prove2me | Theorems.Thm_GlobalTheory_DPEval2_bv_mul
-- name    : GlobalTheory.DPEval2.bv_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:21:35.542218+00:00
-- url     : https://prove2.me/theorems/fe8497e1-72d3-4120-80c5-0ab019dc7917
-- title:
--   DPEval2: bv mul
-- statement:
--   The DPEval2 construction uses the bv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDividedPowerEvalTwoVarsRingHom.lean#L40-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDividedPowerEvalTwoVarsRingHom.lean#L40-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDividedPowerEvalTwoVarsRingHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DPEval2

theorem GlobalTheory.DPEval2.bv_mul (p q : ℕ × ℕ) :
    bv p * bv q = ((p.1 + q.1).choose p.1 * (p.2 + q.2).choose p.2 : ℕ) • bv (p + q) := by sorry
