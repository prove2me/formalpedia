-- Prove2me | Theorems.Thm_GJNSteadyState_Interchange_theorem_2
-- name    : GJNSteadyState.Interchange.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:45.86436+00:00
-- url     : https://prove2.me/theorems/e759e6bd-ee09-4da5-8d68-154f898f2067
-- title:
--   Theorem 2, p. 11 (existence) — a GJN with ρ* < 1 has a stationary distribution
-- statement:
--   Let $\Xi$ be a generalized Jackson network satisfying the standing assumptions of §2.1, and suppose the stability condition
--   $$\rho^*=\max_j\rho_j<1 \tag{3}$$
--   holds. Then the Markov process $\bar Q(t)=(Q(t),\hat a(t),\hat v(t))$ possesses a stationary distribution $\pi$.
--
--   For the heavy-traffic sequence this guarantees that the stationary distributions $\pi^n$ of Theorem 8 exist for all large $n$.
--
--   **Formalization Note** Only the existence clause is stated; uniqueness and convergence require unspecified "additional technical regularity" on the page. Stationarity is `IsStationary`, which includes the existence of a realization from $\pi$.
-- source:
--   Gamarnik and Zeevi, Validity of Heavy Traffic Steady-State Approximations in Generalized Jackson Networks, arXiv:math/0410066v2, p. 11, Theorem 2 (cited: Sigman, Down–Meyn, Dai, Dai–Meyn)

import Mathlib
import Definitions.Def_GJNSteadyState_Interchange_Network
import Definitions.Def_GJNSteadyState_Interchange_Dynamics
open MeasureTheory Filter Topology Matrix

namespace GJNSteadyState.Interchange

/-- Theorem 2 (p. 11, stochastic stability of the GJN), existence clause: if condition (3)
`ρ* < 1` holds, then the Markov process `Q̄` has a stationary distribution. -/
theorem theorem_2 {J : ℕ} (N : Network J) (hN : N.IsGJN) (h3 : ∀ j, rho N j < 1) :
    ∃ π : Measure (State J), IsStationary N π := by sorry

end GJNSteadyState.Interchange
