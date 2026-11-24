-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_TailConst_exists_const_mul_tail
-- name    : GlobalTheory.CompanionTheory.SW.TailConst.exists_const_mul_tail
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:10:09.0229+00:00
-- url     : https://prove2.me/theorems/8d9ef7fb-4069-4ce0-82f9-57486eddaf4f
-- title:
--   Tail Const: exists const mul tail
-- statement:
--   The Tail Const construction uses the exists const mul tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteProductRenormalization.lean#L39-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteProductRenormalization.lean#L39-L82

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteProductMultipliableStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteProductRenormalization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TailConst

theorem GlobalTheory.CompanionTheory.SW.TailConst.exists_const_mul_tail : ∀ (ι : Type) [DecidableEq ι] (a : ι → ℝ) (c : Finset ι → ℝ≥0) (S₁ : Finset ι), (∀ v, 0 ≤ a v) → Summable (fun v => |a v - 1|) → (∀ S, S₁ ⊆ S → ∀ v, v ∉ S → (c S : ℝ) = c (insert v S) * a v) → ∃ (c₀ : ℝ≥0) (S₀ : Finset ι), S₁ ⊆ S₀ ∧ ∀ S, S₀ ⊆ S → (0 < ∏' v : {v // v ∉ S}, a v.1) ∧ (c S : ℝ) = c₀ * ∏' v : {v // v ∉ S}, a v.1 := by sorry
