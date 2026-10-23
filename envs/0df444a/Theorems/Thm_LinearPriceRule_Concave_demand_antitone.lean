-- Prove2me | Theorems.Thm_LinearPriceRule_Concave_demand_antitone
-- name    : LinearPriceRule.Concave.demand_antitone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:59.893344+00:00
-- url     : https://prove2.me/theorems/1a65f569-28f3-4b27-aaf2-182c8d4cd4b8
-- title:
--   Proof of Proposition 5, p. 26 — the demand Q_A(·) is non-increasing on (−∞, P_m], and Q_A(P**) = Q** so Π** = (P** − c)Q_A(P**)
-- statement:
--   Consider a market with maximum price $P_m$, marginal cost $0 \le c < P_m$, saturation quantity $Q_{\max} > 0$ and inverse demand $P_A$ with $P_A(0) = P_m$, non-increasing and continuous on $[0, Q_{\max}]$. Let
--   $$
--   Q_A(p) = \sup\{\,Q \in [0, Q_{\max}] : P_A(Q) \ge p\,\}
--   $$
--   be the demand at price $p$. Then:
--
--   1. $Q_A$ is non-increasing on $(-\infty, P_m]$: if $p \le p' \le P_m$ then $Q_A(p') \le Q_A(p)$;
--   2. every profit-maximizing quantity $Q^{**}$ sells all that is demanded at its own price: $Q_A(P_A(Q^{**})) = Q^{**}$, so $\Pi^{**} = (P^{**} - c)\,Q_A(P^{**})$.
--
--   Both facts are used in the profit chain of the proof of Proposition 5.
--
--   **Formalization Note** No concavity is assumed. Monotonicity is stated for prices up to $P_m$, where the defining set is nonempty.
-- source:
--   Cohen, Perakis & Pindyck, SSRN 2673810, p. 26, proof of Proposition 5

import Mathlib
import Definitions.Def_LinearPriceRule_Concave_Model

namespace LinearPriceRule.Concave
theorem demand_antitone (M : Market) (hM : M.Standing) :
    AntitoneOn (demandAt M) (Set.Iic M.Pm) ∧
    ∀ Q, IsOptQty M Q → demandAt M (M.PA Q) = Q := by sorry
end LinearPriceRule.Concave
