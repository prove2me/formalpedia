-- Prove2me | Theorems.Thm_GreedySuperstring_LowerBound_gap_word_overlap
-- name    : GreedySuperstring.LowerBound.gap_word_overlap
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:04.080187+00:00
-- url     : https://prove2.me/theorems/fd3e694c-7523-4df2-b5bf-dd65c9539af4
-- title:
--   Lemma 4.2 — exact proper overlap of gap words
-- statement:
--   Let $S=[L\mid u_1\cdots u_k\mid R]$ and $T=[L'\mid v_1\cdots v_\ell\mid R']$, with nonnegative pads and positive gaps. Suppose neither is a contiguous substring of the other. Let $J$ consist of all integers $0\le j\le\min(k,\ell)$ satisfying all three tests:
--
--   1. $u_{k-j+i}=v_i$ for every $1\le i\le j$.
--   2. $L'<u_{k-j}$ if $j<k$, and $L'\le L$ if $j=k$.
--   3. $R<v_{j+1}$ if $j<\ell$, and $R\le R'$ if $j=\ell$.
--
--   Then, writing $j_{\max}=\max J$ when $J$ is nonempty,
--
--   $$\operatorname{ov}(S,T)=\begin{cases}[L'\mid v_1\cdots v_{j_{\max}}\mid R],&J\ne\varnothing,\\0^{\min(R,L')},&J=\varnothing.\end{cases}$$
--
--   This includes empty gap lists and $j=0$; the latter describes an overlap with one occurrence of one. It computes the exact overlap word needed throughout the construction, not only its length.
--
--   Differences from the source:
--   - encoding: binary symbols 0 and 1 → the distinct symbol labels [false] and [true] in OAI.Superstring.Word; reason: this renaming preserves contiguous occurrences and counts one symbol per bit, without bit-encoding lengths
--   - encoding: nonnegative pads, one-based gap tests, and max J when J is nonempty → natural pads, zero-based list accesses with guarded endpoints, Boolean tests, and finite supremum of J in the nonempty branch; reason: the suffix-prefix list equality is exactly all j entry equalities; the finite natural supremum is the maximum, and the empty branch never uses it
-- source:
--   Nikolai Chukhin, Rishikesh Gajjala, Juha Harviainen, Alexander S. Kulikov, Ivan Mihajlin, Hiroki Shibata, Alexander V. Smal, The Greedy Superstring Conjecture Is False, STOC 2027 submission #316 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/316.pdf, Lemma 4.2 and standing gap conditions in §4.1, printed p.15 = PDF p.15

import Mathlib
import Definitions.Def_GreedySuperstring_LowerBound_GapModel

namespace GreedySuperstring.LowerBound

/-- Lemma 4.2, printed/PDF p.15, with all pad tests in gapMatches. -/
theorem gap_word_overlap (L R L' R' : ℕ) (u v : List ℕ)
    (hu : ∀ g ∈ u, 0 < g) (hv : ∀ g ∈ v, 0 < g)
    (hst : ¬ gapWord L u R <:+: gapWord L' v R')
    (hts : ¬ gapWord L' v R' <:+: gapWord L u R) :
    overlap (gapWord L u R) (gapWord L' v R') =
      if (gapMatches L R u L' R' v).Nonempty then
        gapWord L' (v.take ((gapMatches L R u L' R' v).sup id)) R
      else List.replicate (min R L') zeroSymbol := by sorry

end GreedySuperstring.LowerBound
