-- Prove2me | Theorems.Thm_MatchingGFT_TightE_theorem_4_1
-- name    : MatchingGFT.TightE.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:13.477533+00:00
-- url     : https://prove2.me/theorems/49165e18-8fbe-4159-a5b3-69388627a36d
-- title:
--   Theorem 4.1 — Tightness
-- statement:
--   For every $\varepsilon>0$ there is a finite market satisfying the assumptions of Theorem 3.1 such that (i) every type law is regular and supported on $[0,1]$; (ii) all trading edges have pairwise disjoint endpoints; (iii) feasibility is one knapsack constraint; (iv) $\mathrm{FB}/E[\mathrm{GFT}(\mathcal M)]\ge e-\varepsilon$ and $\mathrm{FB}/(\frac12(\Pi^S(\mathrm{GSOM})+\Pi^B(\mathrm{GBOM})))\ge e-\varepsilon$.
--
--   Differences from the source:
--   - generalization: one market with its fixed order → (iv) holds for every strict order on the constructed family; reason: the ratios of Proposition 4.3 do not depend on the order; a single order is an instance
--   - encoding: a ratio at least e − ε → a positive denominator and (e − ε)·denominator ≤ FB; reason: Lean division by zero is 0; the denominators are positive in the construction
--   - encoding: a finite market → buyers Fin n and sellers Fin k; reason: every finite market is such up to relabeling
--   - encoding: a knapsack constraint → nonnegative weights and capacity over the matchings of E; reason: as on PDF p. 21; keeps the family downward closed
--   - encoding: K^lin convex on [0, 1], K(1) a left limit that may be +∞ → K^lin convex on [0, 1); reason: the value at 1 is the left limit of the curve, so convexity on [0, 1) is equivalent
--   - encoding: a fixed strict order on the feasible family → an injective rank on the family, smaller rank preferred; reason: every strict order on a finite family arises this way
-- source:
--   Xiaohui Bei, Wenhao Wu, Shengwei Zhou, STOC 2027 submission #465 (October 2026), Theorem 4.1, PDF pp. 18–19

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_MatchingGFT_TightE_Mechanism
import Definitions.Def_MatchingGFT_TightE_Regularity

namespace MatchingGFT.TightE

/-- Theorem 4.1 (PDF pp. 18–19): for every `ε > 0` there is a finite market satisfying the assumptions of
Theorem 3.1 with (i) regular laws supported on `[0, 1]`, (ii) trading edges with pairwise disjoint
endpoints, (iii) a single knapsack constraint, and (iv), under every strict tie-breaking order,
`FB / E[GFT(ℳ)] ≥ e - ε` and `FB / (½(Π^S(GSOM) + Π^B(GBOM))) ≥ e - ε`, written multiplicatively with positive
denominators. -/
theorem theorem_4_1 :
    ∀ ε : ℝ, 0 < ε → ∃ (n k : ℕ) (m : Market (Fin n) (Fin k)), m.IsValid ∧
      (∀ i, IsRegularBuyerLaw (m.buyerLaw i) ∧ IsSupportedOnUnit (m.buyerLaw i)) ∧
      (∀ j, IsRegularSellerLaw (m.sellerLaw j) ∧ IsSupportedOnUnit (m.sellerLaw j)) ∧
      HasDisjointEdges m ∧ IsKnapsackFeasibility m ∧
      ∀ rank : Finset (Fin n × Fin k) → ℕ, IsTieOrder m rank →
        0 < groExpectedGFT m rank ∧
        (Real.exp 1 - ε) * groExpectedGFT m rank ≤ firstBestValue m rank ∧
        0 < (1 / 2) * (profitS m (gsom m rank) + profitB m (gbom m rank)) ∧
        (Real.exp 1 - ε) * ((1 / 2) * (profitS m (gsom m rank) + profitB m (gbom m rank))) ≤
          firstBestValue m rank := by sorry

end MatchingGFT.TightE
