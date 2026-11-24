-- Prove2me | Theorems.Thm_GlobalTheory_GaussCutoff_mem_closure_gauss_mul
-- name    : GlobalTheory.GaussCutoff.mem_closure_gauss_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:29:26.164335+00:00
-- url     : https://prove2.me/theorems/d6629bb7-fe5d-4fdd-8a4f-8ed0ca3e1fc7
-- title:
--   Gauss Cutoff: mem closure gauss mul
-- statement:
--   The Gauss Cutoff construction uses the mem closure gauss mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemClosureWideGaussianMulSchwartz.lean#L132-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemClosureWideGaussianMulSchwartz.lean#L132-L161

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemClosureWideGaussianMulSchwartz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
open scoped ContDiff Nat SchwartzMap
noncomputable section
open GlobalTheory.GaussCutoff

theorem GlobalTheory.GaussCutoff.mem_closure_gauss_mul (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (h : SchwartzMap E ℂ) :
    h ∈ closure {u : SchwartzMap E ℂ | ∃ b : ℝ, 0 < b ∧ ∀ y, u y = Complex.exp (-((b * ‖y‖ ^ 2 : ℝ) : ℂ)) * h y} := by sorry
