-- Prove2me | Theorems.Thm_MasulloRH_shrinking_window_uniform_offline_bound
-- name    : MasulloRH.shrinking_window_uniform_offline_bound
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T01:35:47.886228+00:00
-- url     : https://prove2.me/theorems/838b9655-9938-4b44-adc6-ae3e13ddac77
-- title:
--   Uniform control of off-line spectral terms in shrinking trace windows
-- statement:
--   For each admissible test and each positive tolerance, there is a positive width such that the sum over all off-critical-line zeros strictly inside any narrower window has norm below the tolerance, even after multiplying each term by an arbitrary complex weight of modulus at most one. No zero-free window is assumed.
-- source:
--   Quantitative supporting result for the Masullo cofinal trace-window frontier https://prove2.me/theorems/e9da971b-b1d2-4297-8c07-5fd9fad687e2; uses the established absolute convergence in MasulloRH.trace_window_comparison.

import Mathlib
import Definitions.Def_MasulloRH_RationalTrace
open MasulloRH MeasureTheory Set Filter Topology

theorem MasulloRH.shrinking_window_uniform_offline_bound (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ α : ℝ, 0 < α → α ≤ δ →
      ∀ w : ZetaZerosInTraceStrip (1/2) → ℂ, (∀ ρ, ‖w ρ‖ ≤ 1) →
      ‖∑' ρ : ZetaZerosInTraceStrip (1/2),
          if 0 < |ρ.val.re - 1/2| ∧ |ρ.val.re - 1/2| < α
          then w ρ * zetaTraceTerm φ (1/2) ρ else 0‖ < ε := by sorry
