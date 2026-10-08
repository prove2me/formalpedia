-- Prove2me | Theorems.Thm_GrahamAnomaly_General_chain_sum_le_finish
-- name    : GrahamAnomaly.General.chain_sum_le_finish
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:03:53.078949+00:00
-- url     : https://prove2.me/theorems/430f3d85-998b-402d-b256-3a199a14ac6e
-- title:
--   (3)–(4), proof of Theorem 1, p. 420 — the chain length is at most the first finishing time
-- statement:
--   Let $C=(T_{j_m},\ldots,T_{j_1})$ be a chain under the relaxed precedence order $\prec'\subseteq\prec$. The first run has positive task durations $\mu(T_j)$, a feasible schedule respecting $\prec$, and finishing time $\omega$; the second duration function satisfies $\mu'(T_j)\le\mu(T_j)$ for every task. Then
--
--   $$\sum_{T_j\in C}\mu'(T_j)\le\sum_{T_j\in C}\mu(T_j)\le\omega.$$
--
--   This bounds the work on the second run's covering chain by the time available along the same precedence chain in the first run.
--
--   **Formalization Note** This estimate requires feasibility of the first schedule but does not use its priority list. The chain is a list with consecutive tasks related by $\prec'$; strict transitivity gives the corresponding $\prec$-chain.
-- source:
--   Graham, Bounds on multiprocessing timing anomalies, SIAM J. Appl. Math. 17 (1969), p. 420, displays (3)–(4), proof of Theorem 1; https://doi.org/10.1137/0117039

import Mathlib
import Definitions.Def_GrahamAnomaly_General_Model

namespace GrahamAnomaly.General

/-- Displays (3)–(4): the same chain in the relaxed order is a chain in the
original order, and its processing time cannot exceed the original finish. -/
theorem chain_sum_le_finish {r n : ℕ}
    (μ μ' : Fin r → ℝ) (hμ : ∀ j, 0 < μ j)
    (hle : ∀ j, μ' j ≤ μ j)
    (prec prec' : Fin r → Fin r → Prop)
    [IsStrictOrder (Fin r) prec] [IsStrictOrder (Fin r) prec']
    (hsub : ∀ i j, prec' i j → prec i j)
    (G : Schedule n μ prec) (c : List (Fin r)) (hc : c.Chain' prec') :
    (c.map μ').sum ≤ (c.map μ).sum ∧ (c.map μ).sum ≤ G.finish := by sorry

end GrahamAnomaly.General
