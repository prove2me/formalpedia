-- Prove2me | Theorems.Thm_NonstatRL_Oracle_exists_bounded_optimal_dual
-- name    : NonstatRL.Oracle.exists_bounded_optimal_dual
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T04:28:33.975597+00:00
-- url     : https://prove2.me/theorems/c37195f8-9da4-4bd2-8cd3-a031010e4ae5
-- title:
--   Appendix A.2, p. 33 — bounded optimal dual solution
-- statement:
--   Let $M$ be a finite communicating MDP on a nonempty state set, with a nonempty allowed-action set at every state, and suppose its diameter is at most $D$. Write $\rho^*$ for the optimal value of the occupancy linear program (15). There exists a dual potential $\gamma$ satisfying every constraint of (16) at $\rho=\rho^*$ and
--
--   $$0\le\gamma(s)\le 2D\qquad\text{for every state }s.$$
--
--   This is the bounded optimal dual pair used in the proof of Proposition 1. Dual feasibility at the primal optimum states optimality through linear-program duality.
--
--   **Formalization Note** The state set is required to be nonempty so the existence claim is substantive. The diameter includes return times and minimizes over allowed deterministic stationary policies.
-- source:
--   Cheung, Simchi-Levi & Zhu, Non-Stationary Reinforcement Learning: The Blessing of (More) Optimism, arXiv:1906.02922v4, p. 33, Appendix A.2, first sentence; (15)–(16) and Lemma 2

import Mathlib
import Definitions.Def_FiniteMDPLearning
import Definitions.Def_NonstatRL_Oracle_Model

open BanditAlgorithm ENNReal

namespace NonstatRL.Oracle

/-- The bounded optimal dual solution invoked at the start of Appendix A.2, p. 33. -/
theorem exists_bounded_optimal_dual {S A : ℕ} (M : FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (hS : 0 < S)
    (hAs : ∀ s, (As s).Nonempty) (D : ℝ)
    (hD : diameter M As ≤ ENNReal.ofReal D) :
    ∃ γ : Fin S → ℝ,
      DualFeasible M.r (fun s a s' => (M.P s a s' : ℝ)) As (optGain M As) γ ∧
      ∀ s, 0 ≤ γ s ∧ γ s ≤ 2 * D := by sorry

end NonstatRL.Oracle
