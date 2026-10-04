-- Prove2me | Theorems.Thm_MulmuleyVV_Matching_isolation_perfect_matchings
-- name    : MulmuleyVV.Matching.isolation_perfect_matchings
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:36:10.943975+00:00
-- url     : https://prove2.me/theorems/5c05fc80-d206-4dcf-b12e-11f4979491ee
-- title:
--   §4 — with edge weights uniform in $[1, 2m]$, the minimum weight perfect matching is unique with probability $\ge 1/2$
-- statement:
--   Let $G$ be a graph on $n$ vertices with edge set $E$, $m = |E|$, and suppose $G$ has a perfect matching. Assign to each edge an integer weight chosen uniformly and independently from $\{1, 2, \dots, 2m\}$. Then
--
--   $$
--   \Pr\bigl[\text{the minimum weight perfect matching of } G \text{ is unique}\bigr] \ \ge\ \frac12 .
--   $$
--
--   This is Lemma 1 applied to the set system whose elements are the edges of $G$ and whose sets are its perfect matchings. It is the probabilistic half of the correctness of the matching algorithm.
--
--   **Formalization Note** The sample space is `Fintype.piFinset (fun _ : G.edgeSet => Finset.Icc 1 (2m))` with $m$ = `Fintype.card G.edgeSet`, and the probability bound is $(2m)^m \le 2\cdot\#\{w : \dots\}$. "Unique minimum" is `HasUniqueMin (perfectMatchings G) w`. The hypothesis that $G$ has a perfect matching is the paper's (the input of §4).
-- source:
--   Mulmuley, Vazirani, Vazirani, Matching is as easy as matrix inversion, Combinatorica 7 (1987), pp. 107–108, §4, paragraph spanning the page break (unnumbered)

import Mathlib
import Definitions.Def_MulmuleyVV_Matching_SetSystem
import Definitions.Def_MulmuleyVV_Matching_Algorithm

namespace MulmuleyVV.Matching

open Classical in
theorem isolation_perfect_matchings {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : ∃ M : Finset G.edgeSet, IsPerfectMatchingEdges G M) :
    (2 * Fintype.card G.edgeSet) ^ Fintype.card G.edgeSet ≤
      2 * ((Fintype.piFinset fun _ : G.edgeSet => Finset.Icc 1 (2 * Fintype.card G.edgeSet)).filter
        (fun w => HasUniqueMin (perfectMatchings G) w)).card := by sorry

end MulmuleyVV.Matching
