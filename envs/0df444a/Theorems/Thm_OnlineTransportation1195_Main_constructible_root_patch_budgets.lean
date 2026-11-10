-- Prove2me | Theorems.Thm_OnlineTransportation1195_Main_constructible_root_patch_budgets
-- name    : OnlineTransportation1195.Main.constructible_root_patch_budgets
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:37:17.0914+00:00
-- url     : https://prove2.me/theorems/3bf90d37-aa93-42a2-869f-cd2efbc4d35f
-- title:
--   Lemma 3.3 — constructible root-patch budgets
-- statement:
--   For every positive weighted rooted tree, fixed DFS, and positive root-monotone deadlines with $\sum_e w_e/d_e=1$ that are not all equal, there are $t>0$ and $0\le s\le t$ such that
--
--   $$\left(T_r(t)=\varnothing\ \text{or}\ \sum_{e\in T_r(t)}\frac{w_e}{\min\{d_e,s\}}=1\right),\qquad s+R^{\rm out}(t)\le t,\qquad T_r(t)\ne E.$$
--
--   A single uniform finite arithmetic/comparison program finds these two real numbers in polynomial time. The empty-patch case allows $s=0$; no empty normalized sum is required to equal one. The proper-patch conclusion concerns edge sets, not vertices. The constants in the runtime bound precede every instance.
--
--   Differences from the source:
--   - encoding: finite rooted trees and undirected edges → vertices Fin n and non-root child labels for edges in the referenced positive tree record; reason: every finite rooted positive weighted tree admits this labeling; the root pseudo-edge is ignored
--   - encoding: any fixed root-based depth-first walk and its first-edge downward costs → a vertex list traversing each edge once in each direction; computed x, red edges and root patch; reason: on a tree these are exactly the depth-first tours; the list is fixed before time budgets are quantified
--   - reading: can be computed in polynomial time on positive arbitrary real input → a single rational-literal real RAM program with positive divisions and uniform C(n+1)^d instruction bound; reason: the paper gives no real bit encoding; its construction uses exact arithmetic and comparisons; no mathematical input is restricted
-- source:
--   Anand et al., STOC 2027 submission #1195 (October 2026), Lemma 3.3, PDF / printed p. 9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1195.pdf

import Definitions.Def_OnlineTransportation1195_Main_Computation

namespace OnlineTransportation1195.Main

theorem constructible_root_patch_budgets :
    ∃ (P : SmaleNinth.RAMProgram) (C power : ℕ),
      RationalProgram P ∧ 0 < C ∧
      ∀ (n : ℕ) (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n)),
        T.Normalized d → T.DFS L → T.Unequal d →
        ∃ fuel : ℕ, fuel ≤ C * (n + 1) ^ power ∧
          PositiveDivisions P (treeInput T d L) fuel ∧
          SmaleNinth.RAMHaltedWith P (SmaleNinth.RAMRun P (treeInput T d L) fuel) true ∧
          T.Budget d L
            ((SmaleNinth.RAMRun P (treeInput T d L) fuel).mem (-1))
            ((SmaleNinth.RAMRun P (treeInput T d L) fuel).mem (-2)) := by sorry

end OnlineTransportation1195.Main
