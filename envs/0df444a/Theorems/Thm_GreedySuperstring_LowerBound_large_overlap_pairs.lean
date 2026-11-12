-- Prove2me | Theorems.Thm_GreedySuperstring_LowerBound_large_overlap_pairs
-- name    : GreedySuperstring.LowerBound.large_overlap_pairs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:20.102988+00:00
-- url     : https://prove2.me/theorems/5395118f-fc52-4d26-96b2-152230e584f0
-- title:
--   Lemma 4.3 — the five possible input pairs above beta
-- statement:
--   Fix integers $r\ge1$ and $P\ge r-1$, and form the input set $\mathcal S=\{X_i,Y_i,U_i,V_i,Z_i:1\le i\le r\}$ and $\beta=4P+18r+1$ exactly as in §4.2 and §4.4. For any distinct $s,t\in\mathcal S$,
--
--   $$|\operatorname{ov}(s,t)|>\beta\quad\Longrightarrow\quad\exists\,1\le i\le r:\ (s,t)\in\{(X_i,Y_i),(X_i,V_i),(U_i,Y_i),(U_i,V_i),(Y_i,X_i)\}.$$
--
--   The index is shared by both words. This is a one-way classification with a strict threshold; it does not assert that every listed pair exceeds the threshold at every boundary parameter. It controls all original input pairs for the greedy-validity analysis.
--
--   Differences from the source:
--   - encoding: integers r ≥ 1 and P ≥ r−1 → natural numbers r and P with 1 ≤ r and r ≤ P+1; reason: the source domain already forces both parameters nonnegative, including r=1 and P=0
--   - encoding: binary symbols 0 and 1 → the distinct symbol labels [false] and [true] in OAI.Superstring.Word; reason: this renaming preserves contiguous occurrences and counts one symbol per bit, without bit-encoding lengths
-- source:
--   Nikolai Chukhin, Rishikesh Gajjala, Juha Harviainen, Alexander S. Kulikov, Ivan Mihajlin, Hiroki Shibata, Alexander V. Smal, The Greedy Superstring Conjecture Is False, STOC 2027 submission #316 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/316.pdf, Lemma 4.3, printed p.19 = PDF p.19; construction §4.2 p.16 and beta §4.4 p.19; proof and Tables 1–2 p.20

import Mathlib
import Definitions.Def_GreedySuperstring_LowerBound_Construction

namespace GreedySuperstring.LowerBound

/-- Lemma 4.3, printed/PDF p.19: implication, including all five pair types. -/
theorem large_overlap_pairs (r P : ℕ) (hr : 1 ≤ r) (hP : r ≤ P + 1)
    (s t : OAI.Superstring.Word) (hs : s ∈ inputFamily r P) (ht : t ∈ inputFamily r P)
    (hne : s ≠ t) (hov : beta r P < (overlap s t).length) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ r ∧
      ((s = X r P i ∧ t = Y r P i) ∨
       (s = X r P i ∧ t = V r P i) ∨
       (s = U r P i ∧ t = Y r P i) ∨
       (s = U r P i ∧ t = V r P i) ∨
       (s = Y r P i ∧ t = X r P i)) := by sorry

end GreedySuperstring.LowerBound
