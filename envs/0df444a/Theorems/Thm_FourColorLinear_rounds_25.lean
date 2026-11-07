-- Prove2me | Theorems.Thm_FourColorLinear_rounds_25
-- name    : FourColorLinear.rounds_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:52:15.498199+00:00
-- url     : https://prove2.me/theorems/ebf4729e-1d3c-4c44-9197-817072868680
-- title:
--   The 25 rounds of Kempe changes empty all rings: $p^{L}$ extended per round, $O(\log r)$ rounds (corrected: $\lceil\log_{1/(1-p^L)} r\rceil+1$ rounds)
-- statement:
--   Let $p\in(0,1]$ and $L\in\mathbb N$. Consider rings $A_0$ with levels in $\{1,\dots,L\}$, and repeatedly a set $I_t\subseteq A_t$ with $|I_t|\ge p|A_t|$ whose levels strictly fall, with $A_{t+1}$ those rings of $I_t$ still of positive level. Those of level $0$ are extended. Then
--   $$A_L=\emptyset\qquad\text{and}\qquad \Bigl|\bigcup_{t<L}\{\text{rings extended at step }t\}\Bigr|\ge p^L|A_0|.$$
--   Moreover if the number of empty rings satisfies $r_{j+1}\le(1-p^L)r_j$ then no ring remains after at most $\lceil\log_{1/(1-p^L)}r_0\rceil+1$ rounds. With $p=1/(3\cdot 2^{18})$ and $L=25$ this is the count on p.8.
--
--   This reduces the Kempe-change part of the algorithm to the single-step guarantee of Lemma 11.
--
--   Differences from the source:
--   - generalization: p = 1/(3·2¹⁸) and 25 repetitions → every p ∈ (0,1] and L ∈ ℕ; reason: the count uses nothing else; the printed values specialize it
--   - correction: "after at most log_{1/(1−p²⁵)} r … rounds" → at most ⌈log_{1/(1−p^L)} r₀⌉ + 1 rounds, with the case p^L = 1 stated apart; reason: the printed count is false at r = 1: log_{1/(1−p²⁵)} 1 = 0, yet after 0 rounds one empty ring remains, and one round is needed (r₁ ≤ 1 − p²⁵ < 1); in general r_j ≤ 1 at j = log r, not r_j = 0; the same O(log r)
-- source:
--   Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen, Thorup, Four-Coloring Planar Graphs in Linear Time, arXiv:2610.39753 (held version, sha256 4dce39c5…), §1.2, p.8

import Mathlib

namespace FourColorLinear

/-- The count of the 25 rounds, arXiv:2610.39753 (held version, sha256 4dce39c5…), p.8: "We repeatedly apply Lemma 4 to the active rings,
finding a new Kempe change that improves by a factor of p for the remaining active rings. After 25
repetitions, we know that there are no active rings left, and that at least a fraction p^25 of the
original rings have been extended. Conversely, this means that the number of empty rings has been
reduced by at least a factor 1 − p^25. We now restart with all the empty rings, all of which are
25-extendible. If we started with r reducible configurations, then after at most log_{1/(1−p^25)} r =
O(log r) = O(log n) rounds of 25 Kempe changes, we know that no empty rings remain".

**Formalization Note** `A t` are the active rings, `ℓ t` the levels, `I t` the improved rings; a ring
of `I t` with level 0 is extended and leaves. `L` and `p` are general; `L = 25`, `p = 1/(3·2¹⁸)`
specialize them. The restart count has `+ 1`, since at `r = 1` the logarithm is 0 and one round is
needed. -/
theorem rounds_25 (p : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1) (L : ℕ) :
    (∀ {ι : Type} [DecidableEq ι] (A I : ℕ → Finset ι) (ℓ : ℕ → ι → ℕ),
      (∀ i ∈ A 0, ℓ 0 i ≤ L ∧ 0 < ℓ 0 i) →
      (∀ t, I t ⊆ A t ∧ p * (A t).card ≤ (I t).card ∧ ∀ i ∈ I t, ℓ (t + 1) i < ℓ t i) →
      (∀ t, A (t + 1) = (I t).filter fun i => 0 < ℓ (t + 1) i) →
      A L = ∅ ∧
        p ^ L * (A 0).card ≤
          (((Finset.range L).biUnion fun t =>
            (I t).filter fun i => ℓ (t + 1) i = 0).card : ℝ)) ∧
    ∀ r : ℕ → ℕ, (∀ j, (r (j + 1) : ℝ) ≤ (1 - p ^ L) * r j) →
      (p ^ L = 1 → r 1 = 0) ∧
      (p ^ L < 1 → ∀ j, ⌈Real.logb (1 / (1 - p ^ L)) (r 0)⌉₊ + 1 ≤ j → r j = 0) := by sorry

end FourColorLinear
