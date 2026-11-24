-- Prove2me | Theorems.Thm_GlobalTheory_T_uniform_taylor_bound_levi_pluriharmonic_split
-- name    : GlobalTheory.T.uniform_taylor_bound_levi_pluriharmonic_split
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:01:02.539276+00:00
-- url     : https://prove2.me/theorems/c1b83b58-180c-451d-9fd8-1b967b648004
-- title:
--   T: uniform taylor bound levi pluriharmonic split
-- statement:
--   The T construction uses the uniform taylor bound levi pluriharmonic split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformTaylorBoundLeviPluriharmonicSplitStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformTaylorBoundLeviPluriharmonicSplitStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformTaylorBoundLeviPluriharmonicSplit
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformTaylorBoundLeviPluriharmonicSplitStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.uniform_taylor_bound_levi_pluriharmonic_split : ∀ (n : ℕ) (U K : Set (V n)) (φ : V n → ℝ) (η : ℝ), IsOpen U → IsCompact K → K ⊆ U → ContDiffOn ℝ 2 φ U → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, closedBall z δ ⊆ U ∧ ∃ h : V n → ℂ, Differentiable ℂ h ∧ h 0 = 0 ∧ ∀ w ∈ closedBall (0 : V n) δ, φ (z + w) ≤ φ z + 2 * (h w).re + (leviV n (fun v => (φ v : ℂ)) z fun j => w j).re + η * ‖w‖ ^ 2 := by sorry
