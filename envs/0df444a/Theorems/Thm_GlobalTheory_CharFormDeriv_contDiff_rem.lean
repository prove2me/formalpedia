-- Prove2me | Theorems.Thm_GlobalTheory_CharFormDeriv_contDiff_rem
-- name    : GlobalTheory.CharFormDeriv.contDiff_rem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:21:13.862805+00:00
-- url     : https://prove2.me/theorems/96e63e87-884d-41a0-a6db-deb40390980d
-- title:
--   Char Form Deriv: cont Diff rem
-- statement:
--   The Char Form Deriv construction uses the cont Diff rem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivRemCompLe.lean#L131-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivRemCompLe.lean#L131-L133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open GlobalTheory GlobalTheory.CharFormDeriv

theorem GlobalTheory.CharFormDeriv.contDiff_rem (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (rem t) := by sorry
