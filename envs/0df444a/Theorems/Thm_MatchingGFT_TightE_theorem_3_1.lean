-- Prove2me | Theorems.Thm_MatchingGFT_TightE_theorem_3_1
-- name    : MatchingGFT.TightE.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:00.354295+00:00
-- url     : https://prove2.me/theorems/b578792c-981e-41c3-bcca-0d143b544e2a
-- title:
--   Theorem 3.1 — Main theorem (lower bound)
-- statement:
--   For every finite market in the class and every tie-breaking order, GRO has $E[\mathrm{GFT}(\mathcal M)]\ge\frac1e\mathrm{FB}$, and it is DSIC, ex-post IR and ex-ante WBB.
--
--   Differences from the source:
--   - encoding: a fixed strict order on the feasible family → an injective rank on the family, smaller rank preferred; reason: every strict order on a finite family arises this way
--   - encoding: expected total payments (finite) → ex-ante WBB also states that both expected totals are integrable; reason: makes the Bochner integrals the source expectations
--   - encoding: the expectations are finite (PDF p. 9 for FB) → explicit Integrable conclusions for the GFT of first best, GSOM and GBOM; reason: this makes the Bochner integrals the source expectations; the source treats them as finite
-- source:
--   Xiaohui Bei, Wenhao Wu, Shengwei Zhou, STOC 2027 submission #465 (October 2026), Theorem 3.1, PDF p. 11

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_MatchingGFT_TightE_Mechanism

open MeasureTheory

namespace MatchingGFT.TightE

/-- Theorem 3.1 (PDF p. 11): for every market in the class and every strict tie-breaking order, GRO has
`E[GFT(ℳ)] ≥ (1/e) FB`, all three expectations being finite, and GRO is DSIC, ex-post IR and ex-ante WBB. -/
theorem theorem_3_1 {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]
    (m : Market B S) (hm : m.IsValid) (rank : Finset (B × S) → ℕ) (hrank : IsTieOrder m rank) :
    Integrable (fun t => gft (firstBest m rank t) t) (typeMeasure m) ∧
    Integrable (fun t => gft ((gsom m rank).alloc t) t) (typeMeasure m) ∧
    Integrable (fun t => gft ((gbom m rank).alloc t) t) (typeMeasure m) ∧
    (1 / Real.exp 1) * firstBestValue m rank ≤ groExpectedGFT m rank ∧
    IsDSIC (gro m rank) ∧ IsExPostIR (gro m rank) ∧ IsExAnteWBB m (gro m rank) := by sorry

end MatchingGFT.TightE
