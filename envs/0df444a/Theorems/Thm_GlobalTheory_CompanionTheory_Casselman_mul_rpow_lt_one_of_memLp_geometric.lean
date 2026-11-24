-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Casselman_mul_rpow_lt_one_of_memLp_geometric
-- name    : GlobalTheory.CompanionTheory.Casselman.mul_rpow_lt_one_of_memLp_geometric
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:31:20.715593+00:00
-- url     : https://prove2.me/theorems/d4699d3a-1e67-495f-8106-188a6967fd31
-- title:
--   Casselman: mul rpow lt one of mem Lp geometric
-- statement:
--   The Casselman construction uses the mul rpow lt one of mem Lp geometric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NotMemLpOfGrowth.lean#L7-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NotMemLpOfGrowth.lean#L7-L53

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NotMemLpOfGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Casselman

theorem GlobalTheory.CompanionTheory.Casselman.mul_rpow_lt_one_of_memLp_geometric {X : Type} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (f : X → ℝ) (p : ℝ) (hp : 0 < p)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal p) μ) (E : ℕ → Set X)
    (hE : ∀ j, MeasurableSet (E j)) (hdisj : Pairwise (Function.onFun Disjoint E))
    (c D B r : ℝ) (hc : 0 < c) (hB : 0 < B) (hr : 0 ≤ r)
    (hμ : ∀ j : ℕ, ENNReal.ofReal (c * D ^ j) ≤ μ (E j))
    (hlow : ∀ j : ℕ, ∀ x ∈ E j, B * r ^ j ≤ |f x|) : D * r ^ p < 1 := by sorry
