-- Prove2me | Theorems.Thm_MoneyBurningTrade_IndependentSurplus_lemma_4_6
-- name    : MoneyBurningTrade.IndependentSurplus.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:19.44906+00:00
-- url     : https://prove2.me/theorems/6584e9b9-d21e-47f3-9861-7a8eb3b86171
-- title:
--   Lemma 4.6 — symmetric grid satisfies (19)
-- statement:
--   Let $k\ge2$, $n=2k$, $\delta=1/(100n)$, and let $q$ be the full symmetric grid defined by equation (20). It is a normalized strictly increasing grid, and
--
--   $$q_{j-1}-q_i\le4\delta(q_j-q_{i-1})\qquad(1\le i<j\le n).$$
--
--   This establishes exactly the grid condition used in Definition 4.4, with the source's constant $4$. Incentive validity and surplus separation are not conclusions of this grid lemma.
--
--   Differences from the source:
--   - encoding: the grid in (20), implicitly normalized and ordered → the same explicit grid formula with normalization and strict ordering also stated as conclusions; reason: these are its well-definedness properties; k≥2 and the entire index range are preserved
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Lemma 4.6; equation (20); Appendix A.4, printed p. 27 (PDF p. 28); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_SymmetricGrid

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus

/-- Lemma 4.6 p.27: the full symmetric grid (20) satisfies (19).
Its normalization and strict ordering are included as well-definedness conclusions. -/
theorem lemma_4_6 (k : ℕ) (hk : 2 ≤ k) :
    IsGrid (symmetricGrid k) ∧
    gridCondition (symmetricGrid k) (symmetricDelta k) := by sorry

end MoneyBurningTrade.IndependentSurplus
