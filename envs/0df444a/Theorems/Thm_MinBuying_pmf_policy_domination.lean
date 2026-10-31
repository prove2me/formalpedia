-- Prove2me | Theorems.Thm_MinBuying_pmf_policy_domination
-- name    : MinBuying.pmf_policy_domination
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T18:08:58.962054+00:00
-- url     : https://prove2.me/theorems/ffbf5aa9-09a0-4cc3-8248-03a67e252717
-- title:
--   A posted uniform price dominates every differentiated policy for affiliated exchangeable PMFs
-- statement:
--   Let $w$ be a probability mass function on $n>0$ nonnegative real-valued item valuations. If its law is exchangeable and its real-valued mass function is MTP2, then every feasible differentiated price vector $p$ is weakly dominated in expected revenue by a uniform price equal to one of its coordinates $p_i$. No finite-support or optimal-price-attainment assumption is required. In notation, $$\exists i\in\{1,\ldots,n\}:\ R(w,p)\le R(w,p_i\mathbf 1).$$ The witness is one of the original posted prices, which permits transfer through a coarsening at finitely many thresholds.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, https://doi.org/10.2139/ssrn.5178133 . Theorem 2 and its proof, ec2–ec3, specialized to the PMF alternative of affiliation. The exact posted-price witness is retained for the finite-coarsening transfer.

import Definitions.Def_MinBuying_Symmetry

namespace MinBuying

theorem pmf_policy_domination (n : ℕ) (hn : 0 < n) (w : PMF (Valuations n))
    (hμ : ValidLaw w.toMeasure) (hex : Exchangeable w.toMeasure)
    (hmtp : MTP2 (fun v => (w v).toReal)) (p : Prices n) (hp : FeasiblePrices p) :
    ∃ i : Fin n, Revenue w.toMeasure p ≤ uniformRevenue w.toMeasure (p i) := by
  sorry

end MinBuying
