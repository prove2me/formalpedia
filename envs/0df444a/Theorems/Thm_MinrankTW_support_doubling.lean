-- Prove2me | Theorems.Thm_MinrankTW_support_doubling
-- name    : MinrankTW.support_doubling
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:34:48.075453+00:00
-- url     : https://prove2.me/theorems/18b2fbd8-3b30-4493-b92d-bde00f8924a2
-- title:
--   Section 4, Finish the upper bounds — row/column copies of a width-$w$ decomposition and $\lfloor(2w+2)^2/4\rfloor=(w+1)^2$
-- statement:
--   Let $G$ be a graph on $[n]$, $\mathbb F_q$ a finite field and $S_G$ the entry constraints of graph minrank ($S_{ii}=\{1\}$, $S_{ij}=\mathbb F_q$ on edges, $S_{ij}=\{0\}$ otherwise). Then:
--
--   1. if $(T,(X_s))$ is a tree decomposition of $G$ with bags of at most $w+1$ vertices, replacing every vertex in every bag by its row and column copies gives a tree decomposition of the support graph of $S_G$ with bags of at most $2w+2$ vertices (support width at most $2w+1$);
--   2. the completions of $S_G$ are exactly the normalized fitting matrices of $G$;
--   3. hence for every $j$ the number of rank-$j$ completions of $S_G$ equals the number of rank-$j$ normalized fitting matrices of $G$;
--   4. by scaling rows, every fitting matrix of $G$ has a normalized fitting matrix of the same rank (p.2);
--   5. $\lfloor (2w+2)^2/4\rfloor=(w+1)^2$.
--
--   Applied to Theorem 2 this gives the $q^{(w+1)^2}\mathrm{poly}(n)$ bound of Theorem 1.
--
--   Differences from the source:
--   - generalization: the reduction paragraph of p.15 → adds clause 4, the row-scaling remark of p.2 ("by scaling rows, we may assume w.l.o.g that M_ii = 1"); reason: an extra source conclusion that the reduction uses to pass from normalized witnesses to minrank; it only adds a conclusion
--   - encoding: support width at most 2w + 1 → bags of at most 2w + 2 vertices; reason: width = max |B_t| − 1
--   - encoding: row and column copies of vertex v → Sum.inl v and Sum.inr v; the new bag is the disjoint sum X_s ⊔ X_s; reason: Lean convention
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 4, "Finish the upper bounds", p.15 (with Section 1, p.2)

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition
import Definitions.Def_MinrankTW_Fits
import Definitions.Def_MinrankTW_IsNormalizedFit
import Definitions.Def_MinrankTW_fitCount
import Definitions.Def_MinrankTW_IsCompletion
import Definitions.Def_MinrankTW_supportGraph
import Definitions.Def_MinrankTW_completionCount
import Definitions.Def_MinrankTW_graphConstraints

namespace MinrankTW

/-- **Section 4, "Finish the upper bounds"** (and §1, p.2), Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), p.15. For graph minrank:
1. replacing every vertex in every bag of a tree decomposition of `G` with bags of size at most
   `w + 1` by its row and column copies gives a tree decomposition of the support graph of the
   graph constraints `S_G` (`S_ii = {1}`, `S_ij = F_q` on edges, `{0}` otherwise), with bags of
   size at most `2w + 2` (support width at most `2w + 1`);
2. the completions of `S_G` are exactly the normalized fitting matrices of `G`;
3. hence the number of rank-`j` completions of `S_G` is the number of rank-`j` normalized
   fitting matrices;
4. by scaling rows, every fitting matrix has a normalized fitting matrix of the same rank (p.2);
5. `⌊(2w + 2)²/4⌋ = (w + 1)²`, so Theorem 2 gives `q^{(w+1)²} poly(n)`.

**Formalization Note** The row copy of `v` is `Sum.inl v` and the column copy `Sum.inr v`; the
new bag of node `s` is `X_s ⊔ X_s` (`Finset.disjSum`). -/
theorem support_doubling (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    (∀ (n : ℕ) (T : Type) (G : SimpleGraph (Fin n)) (t : SimpleGraph T) (X : T → Finset (Fin n))
      (w : ℕ), RobertsonSeymour1986.GM5.IsTreeDecomposition G t X → (∀ s, (X s).card ≤ w + 1) →
      RobertsonSeymour1986.GM5.IsTreeDecomposition (supportGraph (graphConstraints F G)) t
          (fun s => (X s).disjSum (X s)) ∧
        ∀ s, ((X s).disjSum (X s)).card ≤ 2 * w + 2) ∧
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (M : Matrix (Fin n) (Fin n) F),
      IsCompletion (graphConstraints F G) M ↔ IsNormalizedFit G M) ∧
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (j : ℕ),
      completionCount (graphConstraints F G) j = fitCount F G j) ∧
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (M : Matrix (Fin n) (Fin n) F),
      Fits G M → ∃ M' : Matrix (Fin n) (Fin n) F, IsNormalizedFit G M' ∧ M'.rank = M.rank) ∧
    ∀ w : ℕ, (2 * w + 2) ^ 2 / 4 = (w + 1) ^ 2 := by sorry

end MinrankTW
