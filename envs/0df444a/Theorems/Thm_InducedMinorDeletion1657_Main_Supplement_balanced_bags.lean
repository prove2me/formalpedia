-- Prove2me | Theorems.Thm_InducedMinorDeletion1657_Main_Supplement_balanced_bags
-- name    : InducedMinorDeletion1657.Main.Supplement.balanced_bags
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:15:27.086565+00:00
-- url     : https://prove2.me/theorems/2e8058e0-c734-425e-b17c-9c524322ccb3
-- title:
--   Lemma 3.4 — balanced separators from bags of a given decomposition
-- statement:
--   There is an absolute positive integer $C$ such that the following holds for every finite graph $G$, every finite tree decomposition $(T,X)$ of $G$, every vertex set $S$, and every positive integer $c$. There is a list of at most $Cc$ nodes of $T$ whose bag union $U$ satisfies
--   $$c\,|S\cap K|\le |S|\quad\text{for every connected component }K\text{ of }G-U.$$
--   Equivalently, each component contains at most $|S|/c$ vertices of $S$. There is no restriction on decomposition width or on connectivity of $G$. An empty list is allowed, including when $S$ is empty. This supplies the balanced bag separator used by the approximation theorem.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → graphs on Fin n, including n = 0; reason: finite relabeling preserves every instance; the base nonnegative treewidth convention changes no nonnegative-width predicate
--   - encoding: r = O(c) nodes of the given rooted tree decomposition → one absolute C > 0 before all instances and a list with length at most C*c; the root is forgotten; reason: a finite tree can be rooted arbitrarily; its bags and components do not change, and the list length is r
--   - encoding: at most |S|/c marked vertices per component → c times the marked component cardinality is at most |S|; reason: c is positive, so multiplication avoids division without changing the inequality
-- source:
--   Daniel Lokshtanov, Fahad Panolan, Saket Saurabh, Jie Xue, Meirav Zehavi, STOC 2027 submission #1657 (October 2026), p. 11 (PDF p. 12), Lemma 3.4; proof printed 11–12 / PDF 12–13

import Definitions.Def_InducedMinorDeletion1657_Main_Graphs
import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition

set_option autoImplicit false
open Classical

namespace InducedMinorDeletion1657.Main.Supplement

/-- Lemma 3.4, printed p.11 / PDF p.12. No width or connectivity bound is imposed. -/
theorem balanced_bags :
  ∃ C : ℕ, 0 < C ∧
    ∀ (n : ℕ) (T : Type) [Fintype T] (G : SimpleGraph (Fin n))
      (tree : SimpleGraph T) (X : T → Finset (Fin n)),
      RobertsonSeymour1986.GM5.IsTreeDecomposition G tree X →
      ∀ (S : Finset (Fin n)) (c : ℕ), 0 < c →
        ∃ xs : List T, xs.length ≤ C * c ∧
          let U := xs.foldl (fun U x => U ∪ X x) ∅
          ∀ K : Set {v : Fin n // v ∉ U}, componentSet (residual G U) K →
            c * (S.filter (fun v => v ∈ Subtype.val '' K)).card ≤ S.card := by sorry

end InducedMinorDeletion1657.Main.Supplement
