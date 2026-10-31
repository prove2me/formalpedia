-- Prove2me | Theorems.Thm_MinBuying_pmf_order_statistics
-- name    : MinBuying.pmf_order_statistics
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T18:08:56.142356+00:00
-- url     : https://prove2.me/theorems/ab6da5f3-da31-4e26-acea-f041ecb04063
-- title:
--   Sorting preserves MTP2 for exchangeable probability mass functions
-- statement:
--   Let $w$ be a probability mass function on $\mathbb R^n$. If the corresponding law is exchangeable and $w$ is MTP2, then the probability mass function of the increasingly sorted valuation vector is MTP2. This includes ties and arbitrary countable support, with no finite-support or distinct-coordinate assumption. Writing $\widetilde w$ for the sorted mass function, the conclusion is $$\widetilde w(x)\widetilde w(y)\le\widetilde w(x\wedge y)\widetilde w(x\vee y).$$ This supplies the order-statistic affiliation needed for the threshold comparison.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, https://doi.org/10.2139/ssrn.5178133 . Supporting lemma for the proof of Theorem 2, ec2–ec3.

import Definitions.Def_MinBuying_Symmetry

namespace MinBuying

/-- Sorting an exchangeable affiliated mass law preserves MTP2, including
the multiplicity factors associated with tied values. -/
theorem pmf_order_statistics (n : ℕ) (w : PMF (Valuations n))
    (hex : Exchangeable w.toMeasure) (hmtp : MTP2 (fun v => (w v).toReal)) :
    MTP2 (fun v => ((w.map (fun z : Valuations n => z ∘ Tuple.sort z)) v).toReal) := by
  sorry

end MinBuying
