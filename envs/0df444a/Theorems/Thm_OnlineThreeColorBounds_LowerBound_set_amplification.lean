-- Prove2me | Theorems.Thm_OnlineThreeColorBounds_LowerBound_set_amplification
-- name    : OnlineThreeColorBounds.LowerBound.set_amplification
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:08.717282+00:00
-- url     : https://prove2.me/theorems/66fe8ca5-445f-42ed-ae55-f7fe0dd25824
-- title:
--   Lemma 2.1 — finite-set amplification
-- statement:
--   Let $P,Q,X$ be finite sets of elements of an arbitrary type, and let $a$ be a real cardinality lower bound and $t$ a nonnegative integer count. Suppose $|P|\ge a$, $|Q|\ge a$, $|X|=t$, and $X\cap P=\varnothing$. With $s=\lceil t/2\rceil$,
--   $$
--   \max\{|P\cup Q|,|Q\cup X|\}\ge a+s.
--   $$
--   This cardinality estimate is the set-theoretic amplification statement used by the bipartite online construction. Both unions are retained in the maximum; no disjointness condition is imposed on $Q$.
--
--   Differences from the source:
--   - encoding: finite sets and their cardinalities → Finset over any decidable-equality type, with natural cardinality t; reason: finite sets admit exactly this representation, with no restriction on their elements
--   - generalization: the cardinality threshold a used as an integer count in the proof → an arbitrary real cardinality lower bound a, with the final cardinality cast to real; reason: apply the integer version at the nonnegative natural ceiling of a; it implies the displayed bound for a, including negative a
--   - encoding: s = ceiling(t/2) for cardinalities t → (t + 1) / 2 in natural arithmetic; reason: these expressions agree exactly for every natural t, including t=0 and odd t
-- source:
--   Yaqiao Li, New bounds for online coloring three-colorable graphs, STOC 2027 submission #425 (October 2026), pinned submission PDF SHA256 ca491d3191fa544c55ed3f45022e4cb14e5570bbd8b8bfb36e98205a8a5c518a, Lemma 2.1, Eq. (2.1), printed p. 5 / PDF p. 6

import Mathlib
set_option autoImplicit false

namespace OnlineThreeColorBounds.LowerBound

/-- Lemma 2.1, printed p. 5 / PDF p. 6. `(t + 1) / 2` is the exact integer ceiling. -/
theorem set_amplification {α : Type*} [DecidableEq α]
    (P Q X : Finset α) (a : ℝ) (t : ℕ) (hP : a ≤ (P.card : ℝ))
    (hQ : a ≤ (Q.card : ℝ))
    (hX : X.card = t) (hXP : Disjoint X P) :
    a + (((t + 1) / 2 : ℕ) : ℝ) ≤ (max (P ∪ Q).card (Q ∪ X).card : ℝ) := by sorry

end OnlineThreeColorBounds.LowerBound
