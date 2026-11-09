-- Prove2me | Theorems.Thm_OnlineThreeColorBounds_LowerBound_bipartite_degree_counting
-- name    : OnlineThreeColorBounds.LowerBound.bipartite_degree_counting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:52.284885+00:00
-- url     : https://prove2.me/theorems/dd821510-bcb9-42d9-9503-2a4d8f141e95
-- title:
--   Lemma 2.2 — degree counting and the degree-two consequence
-- statement:
--   Let $G$ be a finite bipartite simple graph with covering sides $A,B$, and put $a=|A|\ge1$, $b=|B|$. Let the integer $d\ge1$ satisfy $\deg(v)\ge d$ for every $v\in A$. Then, for each integer $1\le i\le a$,
--   $$
--   \left|\{u\in B:\deg(u)\ge i\}\right|\ge
--   \left\lceil\frac{ad-b(i-1)}{a-i+1}\right\rceil.
--   $$
--   In addition,
--   $$
--   a>b\quad\Longrightarrow\quad \left|\{u\in B:\deg(u)\ge2\}\right|\ge d.
--   $$
--   These two conclusions count high-degree vertices on the other side of a bipartition, as needed for the incidence graphs in Lemmas 2.4 and 2.5. The numerator may be negative; the quotient is a real quotient with an integer ceiling, not a truncated natural quotient. The range of $i$ makes the denominator strictly positive.
--
--   Differences from the source:
--   - encoding: two sides of a bipartite graph, and col of a side → Mathlib IsBipartiteWith plus union equal to the entire vertex set, and finset unions of assigned colors; reason: isolated vertices must belong to a side; colors are counted by distinct names and two-sidedness is global across components
--   - encoding: integer ceiling of (ad-b(i-1))/(a-i+1) → Int.ceil of the real quotient, compared with the integer-cast filtered cardinality; reason: real subtraction preserves negative numerators; natural i represents exactly the positive integers 1 through a
-- source:
--   Yaqiao Li, New bounds for online coloring three-colorable graphs, STOC 2027 submission #425 (October 2026), pinned submission PDF SHA256 ca491d3191fa544c55ed3f45022e4cb14e5570bbd8b8bfb36e98205a8a5c518a, Lemma 2.2, Eq. (2.2) and final sentence, printed p. 5 / PDF p. 6

import Definitions.Def_OnlineThreeColorBounds_LowerBound_History
set_option autoImplicit false

namespace OnlineThreeColorBounds.LowerBound

/-- Lemma 2.2, printed p. 5 / PDF p. 6; includes the final degree-two clause.
The quotient is real and its ceiling integer, including when the numerator is negative. -/
theorem bipartite_degree_counting {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s r : Finset V)
    (hparts : CoveringBipartition G s r) (d : ℕ) (hs : 1 ≤ s.card)
    (hd : 1 ≤ d) (hdeg : ∀ v ∈ s, d ≤ G.degree v) :
    (∀ i : ℕ, 1 ≤ i → i ≤ s.card →
      Int.ceil (((s.card : ℝ) * (d : ℝ) - (r.card : ℝ) * ((i : ℝ) - 1)) /
        ((s.card : ℝ) - (i : ℝ) + 1)) ≤
        ((r.filter (fun v => i ≤ G.degree v)).card : ℤ)) ∧
    (r.card < s.card → d ≤ (r.filter (fun v => 2 ≤ G.degree v)).card) := by sorry

end OnlineThreeColorBounds.LowerBound
