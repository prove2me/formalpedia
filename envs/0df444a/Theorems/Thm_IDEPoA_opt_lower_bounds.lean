-- Prove2me | Theorems.Thm_IDEPoA_opt_lower_bounds
-- name    : IDEPoA.opt_lower_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:52:03.033077+00:00
-- url     : https://prove2.me/theorems/0a2cd133-34d8-4e90-8725-933f5faf12ef
-- title:
--   The optima are at least $\max\{\theta_0,1\}$ and $U$ (corrected: $\max\{\theta_0,1\}$ for $\theta_0+1$)
-- statement:
--   Let $\mathcal N$ be an instance with total flow volume $U>0$. Then
--   $$\Theta_{\mathrm{OPT}}(\mathcal N)\ge\max\{\theta_0,1\},\qquad\Xi_{\mathrm{OPT}}(\mathcal N)\ge U.$$
--
--   These bounds turn the upper bounds of Theorem 3.9 into bounds on the prices of anarchy.
--
--   Differences from the source:
--   - generalization: directed graph G = (V, E) with edges vw → finite directed multigraph with tail and head maps, loops and parallel edges allowed; reason: a simple digraph is a special case
--   - reading: f+, f- integrable functions (p.7) → f+, f- integrable on every [0, T]; reason: F+ and F- only need the integral on [0, θ]; global integrability would exclude forever-cycling flows up front, and local integrability contains it
--   - encoding: rates on R≥0, constraints for θ ∈ R≥0 → rates ℝ → ℝ, constraints quantified over 0 ≤ θ; reason: values at negative times play no role
--   - correction: ΘOPT is trivially bounded below by θ0 + 1 → ΘOPT ≥ max{θ0, 1}; reason: the printed bound is false for a non-tight θ0: on one edge st with τ = ν = 1, inflow 1 on [0,1) and θ0 = 5, a feasible flow has makespan 5 < 6; the weaker bound still gives Theorem 3.11
--   - reading: no hypothesis on U → 0 < U; reason: at U = 0, θ0 = 0 the empty flow has makespan 0
--   - generalization: ΞOPT := inf { Ξ(f) | f a feasible flow }, with Ξ(f) of Definition 2.4 stated for terminating flows → infimum over all feasible flows of the formula of Definition 2.4 as a lower integral; reason: the infimum is at most the one over terminating flows, so the Lean bound implies the bound under either reading
-- source:
--   Graf & Harks, The Price of Anarchy for Instantaneous Dynamic Equilibria, arXiv:2007.07794v2, p.22, sentence before Theorem 3.11

import Mathlib
import Definitions.Def_IDEPoA_Model

open MeasureTheory Set
open scoped ENNReal

namespace IDEPoA

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- The lower bounds on the optima (Graf & Harks, arXiv:2007.07794v2, p.22: "Since ΘOPT is trivially
bounded below by θ0 + 1 and ΞOPT by U"), corrected: for positive total volume `U`,
`Θ_OPT ≥ max {θ₀, 1}` and `Ξ_OPT ≥ U`.

The printed `θ₀ + 1` is false when `θ₀` is not tight: on the one-edge network with inflow `1` on
`[0, 1)` and `θ₀ = 5` a feasible flow has makespan `5` (`IDEPoA_oneEdge.lean`). -/
theorem opt_lower_bounds (N : FlowNetwork V E) (hN : Standing N) (hU : 0 < totalVolume N) :
    ENNReal.ofReal (max N.θ₀ 1) ≤ thetaOPT N ∧ ENNReal.ofReal (totalVolume N) ≤ xiOPT N
    := by sorry

end IDEPoA
