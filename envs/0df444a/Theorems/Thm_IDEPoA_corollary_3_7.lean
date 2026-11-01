-- Prove2me | Theorems.Thm_IDEPoA_corollary_3_7
-- name    : IDEPoA.corollary_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:50.986471+00:00
-- url     : https://prove2.me/theorems/dd523954-99c7-4f82-8e11-0d9cbb9cad1f
-- title:
--   Corollary 3.7: if $G$ is sink-like at $\tilde\theta\ge\theta_0$, an IDE terminates before $\tilde\theta+\tau(P_{\max})+\frac12$
-- statement:
--   Let $f$ be an IDE flow and $\tilde\theta\ge\theta_0$ such that the whole graph $G$ is sink-like at time $\tilde\theta$, that is, on the interval $[\tilde\theta,\tilde\theta]$. Then the flow terminates before $\tilde\theta+\tau(P_{\max})+\frac12$:
--   $$\Theta(f)<\tilde\theta+\tau(P_{\max})+\frac12.$$
--
--   Differences from the source:
--   - generalization: directed graph G = (V, E) with edges vw → finite directed multigraph with tail and head maps, loops and parallel edges allowed; reason: a simple digraph is a special case
--   - reading: f+, f- integrable functions (p.7) → f+, f- integrable on every [0, T]; reason: F+ and F- only need the integral on [0, θ]; global integrability would exclude forever-cycling flows up front, and local integrability contains it
--   - encoding: rates on R≥0, constraints for θ ∈ R≥0 → rates ℝ → ℝ, constraints quantified over 0 ≤ θ; reason: values at negative times play no role
--   - encoding: node labels defined by the recursion (6) → label as the infimum of the costs of v-t walks; reason: same function for a feasible flow; the recursion is proved in a verification file
--   - reading: τ(Pmax), the physical length of a longest v-t path → supremum of the lengths of simple v-t paths over all nodes v; reason: the only reading that is finite on a cyclic graph; on an acyclic graph every walk is simple
--   - reading: sink-like at time θ̃ → sink-like on the interval [θ̃, θ̃]; reason: the proof reads it this way
--   - reading: terminates before → strict inequality Θ(f) < …; reason: the proof gives at most τ(Pmax) + vol, with vol < 1/2
-- source:
--   Graf & Harks, The Price of Anarchy for Instantaneous Dynamic Equilibria, arXiv:2007.07794v2, Corollary 3.7, p.17

import Mathlib
import Definitions.Def_IDEPoA_Model

open MeasureTheory Set
open scoped ENNReal

namespace IDEPoA

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- Corollary 3.7 (Graf & Harks, arXiv:2007.07794v2, p.17): an IDE flow for which the whole graph is
sink-like at a time `θ̃ ≥ θ₀` terminates before `θ̃ + τ(Pmax) + 1/2`. -/
theorem corollary_3_7 (N : FlowNetwork V E) (hN : Standing N) (f : Flow E) (hf : IsIDE N f)
    (θtilde : ℝ) (hθ : N.θ₀ ≤ θtilde) (hG : IsSinkLike N f Finset.univ θtilde θtilde) :
    makespan N f < ENNReal.ofReal (θtilde + tauPmax N + 1 / 2) := by sorry

end IDEPoA
