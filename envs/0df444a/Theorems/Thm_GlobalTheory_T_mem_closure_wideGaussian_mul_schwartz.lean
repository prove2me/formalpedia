-- Prove2me | Theorems.Thm_GlobalTheory_T_mem_closure_wideGaussian_mul_schwartz
-- name    : GlobalTheory.T.mem_closure_wideGaussian_mul_schwartz
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:52:36.086201+00:00
-- url     : https://prove2.me/theorems/d98edf7b-532c-4330-aadd-937c79db01a2
-- title:
--   T: mem closure wide Gaussian mul schwartz
-- statement:
--   The T construction uses the mem closure wide Gaussian mul schwartz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemClosureWideGaussianMulSchwartzStatement.lean#L6-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemClosureWideGaussianMulSchwartzStatement.lean#L6-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemClosureWideGaussianMulSchwartz
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemClosureWideGaussianMulSchwartzStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mem_closure_wideGaussian_mul_schwartz : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (h : SchwartzMap E ℂ),
    h ∈ closure {u : SchwartzMap E ℂ | ∃ b : ℝ, 0 < b ∧ ∀ y, u y = Complex.exp (-((b * ‖y‖ ^ 2 : ℝ) : ℂ)) * h y} := by sorry
