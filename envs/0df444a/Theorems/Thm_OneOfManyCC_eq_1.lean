-- Prove2me | Theorems.Thm_OneOfManyCC_eq_1
-- name    : OneOfManyCC.eq_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:53:52.46333+00:00
-- url     : https://prove2.me/theorems/844e83a2-f9d0-4351-840d-2e625f5a578d
-- title:
--   Eq. (1) — every leaf's projected rectangle $S_w\times T_w$ is correct with output $o_w$
-- statement:
--   Let $R\subseteq A\times B\times O$ be a total relation on finite sets, let $1\le k\le\min\{|A|,|B|\}$, and let $P$ be a protocol solving $\mathrm{OneOut}^{\neq}_k(R)$. For each leaf $w$ of $P$ with output $(i_w,o_w)$,
--
--   $$(x,y,o_w)\in R\quad\text{for all }x\in S_w\text{ and }y\in T_w.$$
--
--   Thus the output at a leaf is valid for every pair of inputs that can stand at the named position in tuples reaching the leaf.
--
--   Differences from the source:
--   - generalization: $P$ is the fixed optimal protocol for $\mathrm{OneOut}^{\neq}_k(R)$ → any protocol $P$ solving $\mathrm{OneOut}^{\neq}_k(R)$; reason: optimality is not used; the optimal $P$ is one such protocol
--   - encoding: finite sets $A, B, O$ → Fintype types in `Type`; reason: every finite set is equivalent to a type in `Type`, and this lets the statement quantify over all of them
--   - encoding: positions $[k]=\{1,\dots,k\}$ → 0-based `Fin k`; reason: a relabelling; the paper's index $i$ is `i.val + 1`
--   - encoding: $\mathrm{Inj}_k(A)$ → the embeddings `Fin k ↪ A`; reason: injective maps from $k$ positions are exactly the $k$-tuples of pairwise distinct elements
--   - encoding: a node or leaf of $P$ → its path `List Bool` from the root; reason: leaves with equal labels stay different leaves
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), §5, eq. (1), p.10

import Mathlib
import Definitions.Def_OneOfManyCC_OneOut
import Definitions.Def_OneOfManyCC_LeafSets

namespace OneOfManyCC

/-- **Eq. (1): every leaf's projected rectangle is correct.**
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), §5, eq. (1), p.10:
"Since every pair of tuples in A_w × B_w reaches w and receives the output (i_w, o_w), we have
(x, y, o_w) ∈ R for all x ∈ S_w and y ∈ T_w."

**Formalization Note.** `P` is any protocol solving `OneOut≠ₖ(R)`; the paper's `P` is optimal, and
optimality is not used. -/
theorem eq_1 {A B O : Type} [Fintype A] [Fintype B] [Fintype O] (R : A → B → O → Prop)
    (hR : IsTotal R) (k : ℕ) (hk₁ : 1 ≤ k) (hk : k ≤ min (Fintype.card A) (Fintype.card B))
    (P : Protocol (Fin k ↪ A) (Fin k ↪ B) (Fin k × O))
    (hP : P.SolvesOn (OneOut k R) Set.univ Set.univ)
    (w : List Bool) (i : Fin k) (o : O) (hw : P.leafOutput w = some (i, o))
    (x : A) (hx : x ∈ P.projS w) (y : B) (hy : y ∈ P.projT w) :
    R x y o := by sorry

end OneOfManyCC
