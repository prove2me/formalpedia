-- Prove2me | Theorems.Thm_LewensteinGreedy_Competitive_lemma_6_1
-- name    : LewensteinGreedy.Competitive.lemma_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:32:53.987006+00:00
-- url     : https://prove2.me/theorems/d1f96de5-b6dd-420d-93ec-1981bd7c1421
-- title:
--   Lemma 6.1 — exact inactive-gap quotient
-- statement:
--   Let $n\ge1$, let $X\in[n]^m$ be nonempty and let $h$ be any finite real profile. Run Greedy on $X$ from $h$ and on the quotient sequence $Y=\pi(X)$ over $[N]$ from $\bar h$. Then (i) at every access $t$, the quotient keys touched are exactly the images under $\pi$ of the keys touched in the original execution (the partition intervals containing at least one touched key); and (ii) at every time $t=0,\dots,m$ and for every quotient key $i\in[N]$, the quotient height of $i$ equals the maximum original height of the keys of its interval.
--
--   Differences from the source:
--   - encoding: the same new height in both executions, greater than every current height in either → each execution raises its touched keys to its own maximum height + 1; reason: the two maxima coincide whenever the quotient profile is the partwise maximum of the original one, which is clause (ii) at the previous time; so this is the source's choice
--   - encoding: access t = 1..m, times after each access → 0-based: access t < m reads the profiles after the first t requests; clause (ii) for t ≤ m; reason: Lean list indexing; same instances
--   - encoding: standing universe [n] with n ≥ 1 (§1.2) → explicit hypothesis 1 ≤ n; reason: the source fixes n ≥ 1 for the whole paper
--   - encoding: keys [n] = {1,…,n}, access sequence X ∈ [n]^m → keys are naturals, [n] = Finset.Icc 1 n, X : List ℕ with ValidSequence n X (m = X.length, m = 0 allowed); reason: Lean convention; same instances
--   - encoding: geometric touches defined by empty closed rectangles with earlier points (§2.1.3) → touch set defined by the height-profile rule (2.1) (touches); reason: §2.2 shows the two coincide (only the highest point of each column matters); (2.1) is the source's own operational rule
-- source:
--   Lewenstein, Greedy BST is O(log log n)-Competitive, supplied 2026 artifact (STOC 2027 submission; no DOI/arXiv/URL), SHA-256 04ac49f62855387e9d720867c8d3ded88730274553ff2fb8473a7a53b6906c4f, Lemma 6.1, printed p. 39 / PDF 40

import Mathlib
import Definitions.Def_LewensteinGreedy_Competitive_TouchModel
import Definitions.Def_LewensteinGreedy_Competitive_Greedy
import Definitions.Def_LewensteinGreedy_Competitive_Quotient

namespace LewensteinGreedy.Competitive

/-- Lemma 6.1 (exact inactive-gap quotient), printed p.39 / PDF 40: running Greedy on `X` from `h`
and on `Y = π(X)` from `h̄`, at every access the touched quotient keys are exactly the images of
the touched original keys, and at every time each quotient height is the maximum original height
in its part. -/
theorem lemma_6_1 (n : ℕ) (hn : 1 ≤ n) (X : List ℕ) (hX : ValidSequence n X) (hne : X ≠ [])
    (h : Profile) :
    (∀ t < X.length,
      touches (quotientSize n X) ((quotientSequence n X).getD t 0)
          (profileAfter (quotientSize n X) ((quotientSequence n X).take t)
            (quotientProfile n X h)) =
        (touches n (X.getD t 0) (profileAfter n (X.take t) h)).image (quotientMap n X)) ∧
    (∀ t ≤ X.length, ∀ i ∈ Finset.Icc 1 (quotientSize n X),
      profileAfter (quotientSize n X) ((quotientSequence n X).take t) (quotientProfile n X h) i =
        quotientProfile n X (profileAfter n (X.take t) h) i) := by sorry

end LewensteinGreedy.Competitive
