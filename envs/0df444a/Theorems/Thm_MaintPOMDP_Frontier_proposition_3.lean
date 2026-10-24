-- Prove2me | Theorems.Thm_MaintPOMDP_Frontier_proposition_3
-- name    : MaintPOMDP.Frontier.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T23:02:08.869449+00:00
-- url     : https://prove2.me/theorems/54a6f75e-92da-4efa-8b7b-e09eb3797a09
-- title:
--   Proposition 3, pp. 17–18 — the continuation-cost vector of producing forever, u^(Ṗ) (23) and u_F^(Ṗ) (24)
-- statement:
--   Under the standing assumptions, consider the stationary policy $(\dot P)$ of producing forever, with corrective replacement after each failure. Its continuation-cost vector is
--   $$\mathbf u^{(\dot P)}=\begin{pmatrix}u_0^{(\dot P)}\\u_1^{(\dot P)}\end{pmatrix}=\frac{c^P+\beta\gamma_1c^F}{(1-\beta)[1-\beta+\beta(\gamma_0+\gamma_1)]}\begin{pmatrix}\beta\gamma_0\\1-\beta+\beta\gamma_0\end{pmatrix},\qquad u_F^{(\dot P)}=u_0^{(\dot P)}+c^F .$$
--   Precisely: value iteration with the single action $P$, started from zero terminal costs, converges to $\boldsymbol\pi'\mathbf u^{(\dot P)}$ for every belief $\boldsymbol\pi\ge0$, and its failure coordinate converges to $u_F^{(\dot P)}$.
--
--   The point $\mathbf u^{(\dot P)}$ is the frontier of the "no replacement" structure $[P]$ in Theorems 1 and 2 and the end point of every production sequence.
--
--   **Formalization Note** The cost of a stationary policy is expressed as the limit of value iteration restricted to that policy's action (policy evaluation), in support-function form on unnormalized beliefs.
-- source:
--   Zhang, Zhang, Analytical Solution to a Partially Observable Machine Maintenance Problem with Obvious Failures, SSRN 2945049 (version of 2022-08-21), pp. 17–18, Proposition 3, (23)–(24)

import Mathlib
import Definitions.Def_MaintPOMDP_Frontier_Setting
open Filter Topology

namespace MaintPOMDP.Frontier

/-- Proposition 3 (pp. 17–18): under the stationary policy (Ṗ) of producing forever (the
action set {P} alone), value iteration from zero converges to π′u^(Ṗ) for every belief π ≥ 0 and
to u_F^(Ṗ) in the failure coordinate, with u^(Ṗ) as in (23) and u_F^(Ṗ) = u_0^(Ṗ) + c^F (24). -/
theorem proposition_3 (M : Params) (hM : M.Standing) :
    M.Solves ActSet.P {M.uPdot} M.uFPdot := by sorry

end MaintPOMDP.Frontier
