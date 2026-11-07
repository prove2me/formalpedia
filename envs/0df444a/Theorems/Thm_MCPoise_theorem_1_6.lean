-- Prove2me | Theorems.Thm_MCPoise_theorem_1_6
-- name    : MCPoise.theorem_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:31:32.981415+00:00
-- url     : https://prove2.me/theorems/050070bc-f23c-4e3f-a6c3-a99e1db5c55f
-- title:
--   Theorem 1.6 — a $(1, 1+\lfloor\log_2 k\rfloor)$-junction forest rooted at sources covers half the demands
-- statement:
--   Let $L$ be certified by a subgraph $H^\star \subseteq G$ that connects every demand, with $\Delta(H^\star) \le L$ and $\mathrm{dist}_{H^\star}(s_i, t_i) \le L$.
--
--   **Theorem 1.6.** There are $M \le k$ trees $T_1, \dots, T_M$, with roots that are sources $r_j = s_{a_j}$, and pairwise disjoint sets $D_1, \dots, D_M$ of demand indices, forming a $(1, 1 + \lfloor \log_2 k \rfloor)$-junction forest with
--   $$\Big| \bigcup_{j} D_j \Big| \ge \frac{k}{2}.$$
--   Moreover the trees are vertex-disjoint subgraphs of $H^\star$.
--
--   This shows that the linear program of the paper is feasible with the sources as candidate roots.
--
--   Differences from the source:
--   - generalization: (1, O(log k))-junction forest, edge-disjoint trees → explicit β = 1 + ⌊log₂ k⌋, vertex-disjoint trees, each a subgraph of H⋆, disjoint D_j; reason: this is what the proof gives (pp.35–36) and it implies the printed form; p.6 footnote 1 and p.22 rely on it
--   - generalization: $L$ is the value of the optimal solution → $L$ is an input and the guarantee holds for every $L$ with a certifying subgraph; reason: an optimal solution certifies its own poise, so this contains $L = \mathrm{OPT}$; the proof uses only the certificate (p.35)
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Theorem 1.6, p.7; explicit form, Appendix B, pp.35–36

import Mathlib
import Definitions.Def_MCPoise_WitnessFor
import Definitions.Def_MCPoise_IsJunctionForest

namespace MCPoise

/-- **Theorem 1.6 (existence of a low-poise junction forest).**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Theorem 1.6, p.7: "Given any MC Poise instance, there exists an (1, O(log k))-junction forest that covers at least half of
the terminal pairs. Furthermore, all roots of the junction forest are source terminals; in particular, the number of roots M is at
most k." Explicit form, Appendix B, p.36: "a (1, 1 + ⌊log₂ k⌋)-junction forest covering at least half the demands".

For every `H⋆` certifying `L`: there are `M ≤ k` trees `T_j` with roots `s_{a_j}` forming a `(1, 1 + ⌊log₂ k⌋)`-junction forest
with pairwise disjoint index sets `D_j` that cover at least `k/2` demands. The trees are subgraphs of `H⋆` and vertex-disjoint (p.36).

**Formalization Note.** The bound `1 + ⌊log₂ k⌋` is `β`; `k = 0` gives `M = 0`, and `L = 0` gives one-vertex trees. -/
theorem theorem_1_6 (I : Inst) (L : ℕ) (Hstar : SimpleGraph (Fin I.n)) (hH : WitnessFor I L Hstar) :
    ∃ (M : ℕ) (T : Fin M → I.graph.Subgraph) (a : Fin M → Fin I.k) (D : Fin M → Finset (Fin I.k)),
      M ≤ I.k ∧
      IsJunctionForest I (L : ℝ) 1 ((1 + Nat.log 2 I.k : ℕ) : ℝ) T (fun j => I.s (a j)) D ∧
      (∀ j, (T j).spanningCoe ≤ Hstar) ∧
      (Pairwise fun j j' => Disjoint (T j).verts (T j').verts) ∧
      (Pairwise fun j j' => Disjoint (D j) (D j')) ∧
      I.k ≤ 2 * (Finset.univ.biUnion D).card := by sorry

end MCPoise
