-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_nonneg_avgOver
-- name    : GroundTheory.Automorphic.Parabolic.exists_nonneg_avgOver
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:10:58.871162+00:00
-- url     : https://prove2.me/theorems/d537ed69-9113-55e5-8008-cbbbd33649f1
-- title:
--   Parabolic: exists nonneg avg Over
-- statement:
--   The Parabolic construction uses the exists nonneg avg Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L20-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L20-L53

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
variable {G : Type*} [Group G] {W E : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup E]
  [Module ℂ E]

theorem GroundTheory.Automorphic.Parabolic.exists_nonneg_avgOver (π : W →ₗ[ℂ] E) {K : Subgroup G} {f : G → W} (hf : AvgFinite K f)
    (x : G) (c₀ : E) (hterm : ∀ k ∈ K, ∃ r : ℝ, 0 ≤ r ∧ π (f (x * k)) = (r : ℂ) • c₀) :
    ∃ r : ℝ, 0 ≤ r ∧ π (avgOver K f x) = (r : ℂ) • c₀ ∧
      (∀ r₀ : ℝ, 0 < r₀ → π (f x) = (r₀ : ℂ) • c₀ → c₀ ≠ 0 → 0 < r) := by sorry
