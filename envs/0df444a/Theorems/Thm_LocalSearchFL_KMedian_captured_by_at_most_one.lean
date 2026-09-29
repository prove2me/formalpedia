-- Prove2me | Theorems.Thm_LocalSearchFL_KMedian_captured_by_at_most_one
-- name    : LocalSearchFL.KMedian.captured_by_at_most_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:11:33.185743+00:00
-- url     : https://prove2.me/theorems/ec0ebc39-a32d-4c6c-81a9-209fd7b9ee7d
-- title:
--   A facility $o$ is captured by at most one facility
-- statement:
--   Let $\sigma_S, \sigma_O : C \to F$ be assignments of the clients to facilities and let $o$ be a facility. If facilities $s$ and $s'$ both capture $o$ in the sense of Definition 3.1, that is $|N^o_s| > \tfrac12|N_O(o)|$ and $|N^o_{s'}| > \tfrac12|N_O(o)|$, then
--   $$s = s'.$$
--
--   This is what makes the capture graph a bipartite graph in which every $O$-vertex has degree at most one, and it underlies the choice of the $k$ swaps in the analysis of Theorem 3.2.
--
--   **Formalization Note** The assignments are arbitrary maps; the statement holds in particular for nearest-facility assignments.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 549, remark following Definition 3.1 ("It is easy to see that a facility o ∈ O is captured by at most one facility in S.")

import Mathlib
import Definitions.Def_LocalSearchFL_KMedian_captures

namespace LocalSearchFL.KMedian

/-- Remark after Definition 3.1 (p. 549): a facility `o` is captured by at most one facility. -/
theorem captured_by_at_most_one {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (o s s' : Fa)
    (hs : captures σS σO s o) (hs' : captures σS σO s' o) : s = s' := by sorry

end LocalSearchFL.KMedian
