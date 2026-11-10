-- Prove2me | Theorems.Thm_OnlineTransportation1195_Main_weighted_tree_walk_deadlines
-- name    : OnlineTransportation1195.Main.weighted_tree_walk_deadlines
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:37:01.628877+00:00
-- url     : https://prove2.me/theorems/e1730335-25dd-446e-a990-95230a960196
-- title:
--   Theorem 1.3 — full weighted tree walk with deadlines
-- statement:
--   Let $T$ be an $n$-vertex rooted tree with arbitrary positive real edge weights nondecreasing along every root path. There exists a walk $L$ starting at the root and visiting every edge, such that
--
--   $$\operatorname{totalWeight}(L\text{ through the first crossing of }e)\le(2n-3)w_e\quad(e\in E).$$
--
--   Both directions of every traversal are charged. A single uniform finite real arithmetic/comparison program computes the walk in polynomial time; its executed instruction count and emitted walk length have uniform bounds $C(n+1)^d$. The constants precede all input trees. The singleton tree is included, with the zero-traversal walk represented by its root. This retains both numbered clauses and the last computational sentence.
--
--   Differences from the source:
--   - encoding: finite rooted trees and undirected edges → vertices Fin n and non-root child labels for edges in the referenced positive tree record; reason: every finite rooted positive weighted tree admits this labeling; the root pseudo-edge is ignored
--   - reading: can be computed in polynomial time on positive arbitrary real input → a single rational-literal real RAM program with positive divisions and uniform C(n+1)^d instruction bound; reason: the paper gives no real bit encoding; its construction uses exact arithmetic and comparisons; no mathematical input is restricted
--   - encoding: walk computed in polynomial time → output vertex list with every coordinate checked in written memory and polynomial length; reason: the explicit output convention charges scalar writes and the vertex list includes the initial root
-- source:
--   Anand et al., STOC 2027 submission #1195 (October 2026), Theorem 1.3, PDF / printed p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1195.pdf

import Definitions.Def_OnlineTransportation1195_Main_Computation

namespace OnlineTransportation1195.Main

theorem weighted_tree_walk_deadlines :
    ∃ (P : SmaleNinth.RAMProgram) (C power : ℕ),
      RationalProgram P ∧ 0 < C ∧
      ∀ (n : ℕ) (T : Tree n), T.Monotone T.W →
        ∃ (fuel : ℕ) (L : List (Fin n)),
          fuel ≤ C * (n + 1) ^ power ∧ L.length ≤ C * (n + 1) ^ power ∧
          PositiveDivisions P (treeInput T (fun _ => 0) []) fuel ∧
          SmaleNinth.RAMHaltedWith P
            (SmaleNinth.RAMRun P (treeInput T (fun _ => 0) []) fuel) true ∧
          OutputsWalk (SmaleNinth.RAMRun P (treeInput T (fun _ => 0) []) fuel) L ∧
          T.TotalDeadlines L (fun e => (2 * (n : ℝ) - 3) * T.W e) := by sorry

end OnlineTransportation1195.Main
