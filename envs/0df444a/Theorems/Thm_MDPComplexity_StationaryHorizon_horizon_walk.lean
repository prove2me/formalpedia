-- Prove2me | Theorems.Thm_MDPComplexity_StationaryHorizon_horizon_walk
-- name    : MDPComplexity.StationaryHorizon.horizon_walk
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:44:37.58577+00:00
-- url     : https://prove2.me/theorems/5dc01fba-6b81-47b0-a0ca-e9d9f9bbfd31
-- title:
--   The horizon-T policy optimum equals the cheapest T-arc walk
-- statement:
--   Let $M$ be a finite stationary deterministic process, $s_0$ an initial state, and $T\ge0$. A policy may depend on both state and time, and a walk remembers the chosen decision on every arc. Then
--
--   $$J_T^*(s_0)=\min\{c(W):W\text{ is a }T\text{-arc walk beginning at }s_0\}.$$
--
--   This identifies the policy problem with the weighted graph problem used in the proof of Theorem 5.
--
--   **Formalization Note** Horizon $T$ means exactly $T$ decisions here, as in the theorem's graph paragraph. The minimum is attained because the horizon and all statewise decision sets are finite and nonempty.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 447, §3 The finite horizon, stationary case, first sentence, https://doi.org/10.1287/moor.12.3.441

import Mathlib
import Definitions.Def_MDPComplexity_StationaryHorizon_Model

namespace MDPComplexity.StationaryHorizon

variable {S : Type} [Fintype S]

/-- §3, p. 447: the deterministic stationary horizon problem is the cheapest walk with
exactly `T` decision arcs from the initial state. -/
theorem horizon_walk (M : DetMDP S) (s₀ : S) (T : ℕ) :
    IsLeast {y : ℝ | ∃ W : M.Walk T, W.x 0 = s₀ ∧ y = W.cost}
      (M.optHorizon s₀ T) := by sorry

end MDPComplexity.StationaryHorizon
