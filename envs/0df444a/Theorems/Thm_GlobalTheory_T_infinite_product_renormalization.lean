-- Prove2me | Theorems.Thm_GlobalTheory_T_infinite_product_renormalization
-- name    : GlobalTheory.T.infinite_product_renormalization
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:25.569267+00:00
-- url     : https://prove2.me/theorems/5a7b9e1e-543e-548f-a887-0e61e5b6551f
-- title:
--   T: infinite product renormalization
-- statement:
--   The T construction uses the infinite product renormalization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteProductRenormalizationStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteProductRenormalizationStatement.lean#L6-L7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteProductRenormalization
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteProductRenormalizationStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.infinite_product_renormalization : ∀ (ι : Type) [DecidableEq ι] (a : ι → ℝ) (c : Finset ι → ℝ≥0) (S₁ : Finset ι), (∀ v, 0 ≤ a v) → Summable (fun v => |a v - 1|) → (∀ S, S₁ ⊆ S → ∀ v, v ∉ S → (c S : ℝ) = c (insert v S) * a v) → ∃ (c₀ : ℝ≥0) (S₀ : Finset ι), S₁ ⊆ S₀ ∧ ∀ S, S₀ ⊆ S → (0 < ∏' v : {v // v ∉ S}, a v.1) ∧ (c S : ℝ) = c₀ * ∏' v : {v // v ∉ S}, a v.1 := by sorry
