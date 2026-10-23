-- Prove2me | Theorems.Thm_KellyStochasticNetworks_FlowStability_supporting_utility
-- name    : KellyStochasticNetworks.FlowStability.supporting_utility
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:49:23.145975+00:00
-- url     : https://prove2.me/theorems/cf2f3764-c1f2-444b-978f-b47b3ed5e04a
-- title:
--   Eq. (8.5) — supporting-utility inequality
-- statement:
--   Let $X(n)$ be a weighted $\alpha$-fair allocation and fix a count vector $n$. Let $U\ge0$ satisfy $AU\le C$ and be positive on active routes. For the aggregate objective $G_n$ of (8.4),
--   $$\sum_{r:n_r>0}w_rn_r^\alpha U_r^{-\alpha}(U_r-X_r(n))\le G_n(U)-G_n(X(n))\le0.$$
--   Both parts of the displayed source inequality are retained. It relates the utility difference to the weighted expression used in the Lyapunov analysis.
--
--   **Formalization Note** “Inside” the feasible region is interpreted on active coordinates, where the displayed gradient exists. Inactive coordinates contribute zero and may have any feasible nonnegative value in $U$; they are not required to match the allocation's zero convention. Resource constraints may be tight. All positive values of $\alpha$, including one, are covered.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed p. 190 (PDF p. 198), Eq. (8.5)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_FlowStability_Network

namespace KellyStochasticNetworks.FlowStability

/-- Eq. (8.5): both inequalities, including the intermediate utility difference.
U is interior on active coordinates, where the source's G'(U) exists. -/
theorem supporting_utility {J R : ℕ} (D : Network J R)
    (X : State R → Fin R → ℝ) (hX : IsAlphaFair D X)
    (n : State R) (U : Fin R → ℝ)
    (hU : U ∈ KellyStochasticNetworks.networkFeasible D.A D.C)
    (hUpos : ∀ r, 0 < n r → 0 < U r) :
    (∑ r ∈ Finset.univ.filter (fun r => 0 < n r),
      D.w r * (n r : ℝ) ^ D.alpha * U r ^ (-D.alpha) * (U r - X n r))
      ≤ aggregateUtility D n U - aggregateUtility D n (X n) ∧
    aggregateUtility D n U - aggregateUtility D n (X n) ≤ 0 := by sorry

end KellyStochasticNetworks.FlowStability
