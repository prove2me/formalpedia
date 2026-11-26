-- Prove2me | Theorems.Thm_FriedCrossing_Crossing_crossing_exists_unique_local
-- name    : FriedCrossing.Crossing.crossing_exists_unique_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:41:47.816798+00:00
-- url     : https://prove2.me/theorems/1e45b4e3-0ca8-4be0-a5ac-1ac662153440
-- title:
--   Crossing: crossing exists unique local
-- statement:
--   LOCAL crossing lemma. A real branch differentiable on |τ| < δ with ∂_τ s ≥ r > 0
--   there, s(0) < 0 and |s(0)| < rδ, crosses 0 exactly once in (−δ, δ), at
--   σ ∈ (0, |s(0)|/r] ⊂ (0, δ).
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L256-L301
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean#L256-L301

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.Crossing

theorem FriedCrossing.Crossing.crossing_exists_unique_local {s ds : ℝ → ℝ} {r δ : ℝ} (hr : 0 < r)
    (hderiv : ∀ τ, |τ| < δ → HasDerivAt s (ds τ) τ) (hlow : ∀ τ, |τ| < δ → r ≤ ds τ)
    (hs0 : s 0 < 0) (hsmall : |s 0| < r * δ) :
    ∃ σ, 0 < σ ∧ σ ≤ |s 0| / r ∧ σ < δ ∧ s σ = 0 ∧ ∀ τ, |τ| < δ → s τ = 0 → τ = σ := by sorry
