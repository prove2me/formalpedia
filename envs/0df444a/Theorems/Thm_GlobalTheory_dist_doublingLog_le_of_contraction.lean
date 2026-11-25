-- Prove2me | Theorems.Thm_GlobalTheory_dist_doublingLog_le_of_contraction
-- name    : GlobalTheory.dist_doublingLog_le_of_contraction
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:01:41.77902+00:00
-- url     : https://prove2.me/theorems/3adba9ce-a8c7-430b-8ea3-3ede93f7275a
-- title:
--   Global Theory: dist doubling Log le of contraction
-- statement:
--   The Global Theory construction uses the dist doubling Log le of contraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoUniformlyOnDoublingLogOfContraction.lean#L104-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoUniformlyOnDoublingLogOfContraction.lean#L104-L111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter Asymptotics
open scoped Topology
open GlobalTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {ε : V → V} {r C : ℝ}
variable [CompleteSpace V]

theorem GlobalTheory.dist_doublingLog_le_of_contraction (hc : ∀ x ∈ ball (0 : V) r, ‖ε x‖ ≤ 5 / 8 * ‖x‖)
    (hC0 : 0 ≤ C) (hC : ∀ x ∈ ball (0 : V) r, ‖ε x - (2 : ℂ)⁻¹ • x‖ ≤ C * ‖x‖ ^ 2)
    {x : V} (hx : x ∈ ball (0 : V) r) (j : ℕ) :
    dist ((2 : ℂ) ^ j • ε^[j] x) (doublingLog ε x) ≤ 64 / 7 * C * ‖x‖ ^ 2 * (25 / 32) ^ j := by sorry
