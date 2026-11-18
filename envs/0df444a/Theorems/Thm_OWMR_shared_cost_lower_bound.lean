-- Prove2me | Theorems.Thm_OWMR_shared_cost_lower_bound
-- name    : OWMR.shared_cost_lower_bound
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T01:17:25.660213+00:00
-- url     : https://prove2.me/theorems/014e50d5-3fe3-4326-a252-73a75f1769aa
-- title:
--   Shared-cost lower bound (Proposition 3)
-- statement:
--   This is the shared-cost lower bound (Proposition 3 of the source).
--
--   Consider an OWMR network that satisfies the standing assumptions and in which every retailer's holding rate is at least the warehouse rate, $H_i\ge h$ for all $i$, and let $x$ be a valid initial state. Then for every real $\gamma>1$,
--
--   $$J_0(\gamma K_0)+(\gamma-1)\sum_{i=1}^nJ_i\!\left(\frac{\gamma K_i}{\gamma-1}\right)\le\gamma\,\mathrm{OPT}.$$
--
--   Here $J_0(k)$ is the optimal average cost of the supplier's single-location problem (aggregate demand, cost $f_{L_0}$, setup cost $k$), $J_i(k)$ is that of retailer $i$ (its own demand, cost $F_i$, setup cost $k$), and $\mathrm{OPT}$ is the infimum of the long-run average expected cost over all nonanticipative feasible policies from $x$, including history-dependent and randomized ones.
--
--   The bound splits $\gamma$ copies of the physical cost between one pooled supplier problem and $\gamma-1$ copies of each retailer problem. It is the lower half of the proof of Theorem 1, and the source also compares the consolidation policy with it in the proof of Theorem 2.
--
--   **Formalization Note** Costs are extended nonnegative reals; the factors $\gamma$ and $\gamma-1$ enter through `ENNReal.ofReal`.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 5.3, Proposition 3 (Shared-Cost Lower Bound), eq. (28), p. 24.

import Definitions.Def_owmr_single_location

open scoped ENNReal

namespace OWMR
theorem shared_cost_lower_bound {n : ℕ} (N : Network n) (hN : N.Standing)
    (hH : ∀ i, N.h ≤ N.H i) (x : InitState n) (hx : x.Valid) (γ : ℝ) (hγ : 1 < γ) :
    N.J0 (γ * N.K0) + ENNReal.ofReal (γ - 1) * ∑ i, N.J i (γ * N.K i / (γ - 1))
      ≤ ENNReal.ofReal γ * OPT N x := by sorry
end OWMR
