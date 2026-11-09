-- Prove2me | Theorems.Thm_MatchingGFT_TightE_theorem_1_1
-- name    : MatchingGFT.TightE.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:15.011438+00:00
-- url     : https://prove2.me/theorems/5f0d9c18-6eab-45e5-9d09-8fe2617a75cb
-- title:
--   Theorem 1.1 — GRO attains exactly the 1/e fraction of first best
-- statement:
--   The conjunction of Theorem 3.1 in full (the $1/e$ guarantee on every finite market in the class with every tie-breaking order, with DSIC, ex-post IR and ex-ante WBB) and Theorem 4.1 in full (clauses (i)–(iv)).
--
--   Differences from the source:
--   - reading: the informal Theorem 1.1 → the conjunction of Theorems 3.1 and 4.1; reason: the source says its formal statements appear in those theorems (PDF p. 4)
--   - generalization: one market with its fixed order in the tightness part → (iv) holds for every strict order on the constructed family; reason: a single order is an instance
--   - encoding: a ratio at least e − ε → a positive denominator and (e − ε)·denominator ≤ FB; reason: Lean division by zero is 0
--   - encoding: expectations are finite → explicit Integrable conclusions; reason: makes the Bochner integrals the source expectations
--   - encoding: a finite market in the tightness part → buyers Fin n and sellers Fin k; reason: every finite market is such up to relabeling
--   - encoding: a knapsack constraint → nonnegative weights and capacity over the matchings of E; reason: as on PDF p. 21; keeps the family downward closed
--   - encoding: K^lin convex on [0, 1], K(1) a left limit that may be +∞ → K^lin convex on [0, 1); reason: the value at 1 is the left limit of the curve, so convexity on [0, 1) is equivalent
--   - encoding: expected total payments (finite) → ex-ante WBB also states that both expected totals are integrable; reason: makes the Bochner integrals the source expectations
--   - encoding: a fixed strict order on the feasible family → an injective rank on the family, smaller rank preferred; reason: every strict order on a finite family arises this way
-- source:
--   Xiaohui Bei, Wenhao Wu, Shengwei Zhou, STOC 2027 submission #465 (October 2026), Theorem 1.1, PDF p. 4; formally Theorem 3.1, PDF p. 11, and Theorem 4.1, PDF pp. 18–19

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_MatchingGFT_TightE_Mechanism
import Definitions.Def_MatchingGFT_TightE_Regularity

open MeasureTheory

namespace MatchingGFT.TightE

/-- Theorem 1.1 (PDF p. 4), formally Theorem 3.1 and
Theorem 4.1 in full: GRO obtains at least a `1/e` fraction of first-best GFT and is DSIC, ex-post IR and
ex-ante WBB on every market in the class, and this guarantee is tight over the class. -/
theorem theorem_1_1 :
    (∀ {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]
      (m : Market B S), m.IsValid → ∀ rank : Finset (B × S) → ℕ, IsTieOrder m rank →
      Integrable (fun t => gft (firstBest m rank t) t) (typeMeasure m) ∧
      Integrable (fun t => gft ((gsom m rank).alloc t) t) (typeMeasure m) ∧
      Integrable (fun t => gft ((gbom m rank).alloc t) t) (typeMeasure m) ∧
      (1 / Real.exp 1) * firstBestValue m rank ≤ groExpectedGFT m rank ∧
      IsDSIC (gro m rank) ∧ IsExPostIR (gro m rank) ∧ IsExAnteWBB m (gro m rank)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ (n k : ℕ) (m : Market (Fin n) (Fin k)), m.IsValid ∧
      (∀ i, IsRegularBuyerLaw (m.buyerLaw i) ∧ IsSupportedOnUnit (m.buyerLaw i)) ∧
      (∀ j, IsRegularSellerLaw (m.sellerLaw j) ∧ IsSupportedOnUnit (m.sellerLaw j)) ∧
      HasDisjointEdges m ∧ IsKnapsackFeasibility m ∧
      ∀ rank : Finset (Fin n × Fin k) → ℕ, IsTieOrder m rank →
        0 < groExpectedGFT m rank ∧
        (Real.exp 1 - ε) * groExpectedGFT m rank ≤ firstBestValue m rank ∧
        0 < (1 / 2) * (profitS m (gsom m rank) + profitB m (gbom m rank)) ∧
        (Real.exp 1 - ε) * ((1 / 2) * (profitS m (gsom m rank) + profitB m (gbom m rank))) ≤
          firstBestValue m rank) := by sorry

end MatchingGFT.TightE
