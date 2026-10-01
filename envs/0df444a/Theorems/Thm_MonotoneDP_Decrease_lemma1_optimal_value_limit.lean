-- Prove2me | Theorems.Thm_MonotoneDP_Decrease_lemma1_optimal_value_limit
-- name    : MonotoneDP.Decrease.lemma1_optimal_value_limit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:03:12.022785+00:00
-- url     : https://prove2.me/theorems/0be89bd9-7a9a-46b0-8ed9-3b73794a4f5a
-- title:
--   Lemma 1 — under D, J* is the limit of the N-stage optimal values J_N
-- statement:
--   Consider the abstract dynamic programming model of Bertsekas (1977): monotone mapping $H$, terminal function $\bar J>-\infty$, policies $\pi=\{\mu_0,\mu_1,\dots\}$ with cost $J_\pi=\lim_N(T_{\mu_0}\cdots T_{\mu_{N-1}})(\bar J)$, and optimal value $J^*=\inf_\pi J_\pi$. For $N\ge1$ let
--
--   $$J_N(x)=\inf_{\pi\in\Pi}(T_{\mu_0}\cdots T_{\mu_{N-1}})(\bar J)(x)$$
--
--   be the optimal value function of the $N$-stage problem (36). If Assumption D ($\bar J\ge H(\cdot,u,\bar J)$) holds, then for every $x\in S$
--
--   $$J^*(x)=\lim_{N\to\infty}J_N(x).\tag{44}$$
--
--   This says that under uniform decrease the infinite-horizon optimal value is the limit of the finite-horizon optimal values; it is the first half of the proof that the dynamic programming algorithm converges under D.
--
--   **Formalization Note** The limit is taken pointwise in $[-\infty,\infty]$ with its order topology, as `Tendsto (fun N => J_N x) atTop (𝓝 (J* x))`.
-- source:
--   Bertsekas, Monotone Mappings with Application in Dynamic Programming, SIAM J. Control Optim. 15 (1977), p. 453 (PDF p. 16), Lemma 1, eq. (44). DOI 10.1137/0315031

import Mathlib
import Definitions.Def_MonotoneDP_Decrease_Model
import Definitions.Def_MonotoneDP_Decrease_Assumptions

namespace MonotoneDP.Decrease

open Filter Topology

/-- Bertsekas (1977), p. 453, Lemma 1: under D, `J* = lim_{N → ∞} J_N` pointwise, where `J_N` is
the optimal value function of the `N`-stage problem (36). -/
theorem lemma1_optimal_value_limit {S C : Type*} (m : Model S C) (hD : m.AssumptionD) :
    ∀ x, Tendsto (fun N => m.JN N x) atTop (𝓝 (m.Jstar x)) := by sorry

end MonotoneDP.Decrease
