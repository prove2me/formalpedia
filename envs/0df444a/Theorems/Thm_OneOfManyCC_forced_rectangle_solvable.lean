-- Prove2me | Theorems.Thm_OneOfManyCC_forced_rectangle_solvable
-- name    : OneOfManyCC.forced_rectangle_solvable
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:54:42.496581+00:00
-- url     : https://prove2.me/theorems/368a61af-a638-4f10-976e-dc722dec8803
-- title:
--   §5, proof of Lemma 5.2 — the forced rectangle $A'\times B'$ is solvable
-- statement:
--   Let $R$ be a total relation on finite sets, $1\le k\le\min\{|A|,|B|\}$, and $P$ an optimal protocol for $\mathrm{OneOut}^{\neq}_k(R)$, of depth $\mathrm{CC}(\mathrm{OneOut}^{\neq}_k(R))$. Fix $i\in[k]$ and split the leaves $w$ with $i_w\ne i$ into disjoint sets $L'$ and $L''$. Let
--
--   $$A'=\{x\in A : \text{Alice can force }L'\cup\{w : i_w=i,\ x\in S_w\}\},$$
--
--   $$B'=\{y\in B : \text{Bob can force }L''\cup\{w : i_w=i,\ y\in T_w\}\}.$$
--
--   Then the rectangle $A'\times B'$ is solvable. This is the step where the tuple protocol becomes a protocol for $R$ on single inputs, with no increase in depth.
--
--   Differences from the source:
--   - encoding: $\log$ inside $O(\cdot)$ and $\lceil\log_2\cdot\rceil$ → `Real.logb 2` and `Nat.clog 2`; reason: the paper's logarithms are base 2; `Nat.clog 2 m` is $\lceil\log_2 m\rceil$ for $m\ge1$ and `Real.logb 2 0 = 0`
--   - generalization: the partition $L',L''$ obtained after fixing the coordinates $x_j,y_j$, $j\ne i$ → an arbitrary partition of the leaves with $i_w\ne i$; reason: the printed argument uses only that $L',L''$ are disjoint and cover those leaves; the paper's partition is one such
--   - encoding: finite sets $A, B, O$ → Fintype types in `Type`; reason: every finite set is equivalent to a type in `Type`, and this lets the statement quantify over all of them
--   - encoding: positions $[k]=\{1,\dots,k\}$ → 0-based `Fin k`; reason: a relabelling; the paper's index $i$ is `i.val + 1`
--   - encoding: $\mathrm{Inj}_k(A)$ → the embeddings `Fin k ↪ A`; reason: injective maps from $k$ positions are exactly the $k$-tuples of pairwise distinct elements
--   - encoding: a node or leaf of $P$ → its path `List Bool` from the root; reason: leaves with equal labels stay different leaves
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), §5, proof of Lemma 5.2, p.11

import Mathlib
import Definitions.Def_OneOfManyCC_Solvable
import Definitions.Def_OneOfManyCC_LeafSets
import Definitions.Def_OneOfManyCC_Forcing

namespace OneOfManyCC

/-- **The forced rectangle is solvable.**
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), §5, proof of Lemma 5.2, p.11:
"Let A′ be the set of x ∈ A for which Alice can force L′ ∪ {w : i_w = i, x ∈ S_w}, and let B′ be the
set of y ∈ B for which Bob can force L′′ ∪ {w : i_w = i, y ∈ T_w}. The rectangle A′ × B′ is
solvable".

**Formalization Note.** `P` is an optimal protocol for `OneOut≠ₖ(R)`, as in the paper. `L'`, `L''` are
an arbitrary partition of the leaves with `i_w ≠ i`; the paper's partition comes from a fixing of the
other coordinates. -/
theorem forced_rectangle_solvable {A B O : Type} [Fintype A] [Fintype B] [Fintype O]
    (R : A → B → O → Prop) (hR : IsTotal R) (k : ℕ) (hk₁ : 1 ≤ k)
    (hk : k ≤ min (Fintype.card A) (Fintype.card B))
    (P : Protocol (Fin k ↪ A) (Fin k ↪ B) (Fin k × O))
    (hP : P.SolvesOn (OneOut k R) Set.univ Set.univ) (hdepth : P.depth = CC (OneOut k R))
    (i : Fin k) (L' L'' : Set (List Bool)) (hdisj : Disjoint L' L'')
    (hunion : L' ∪ L'' = {w | ∃ j, P.HasIndex w j ∧ j ≠ i}) :
    Solvable k R
      {x | P.AliceForces (L' ∪ {w | P.HasIndex w i ∧ x ∈ P.projS w})}
      {y | P.BobForces (L'' ∪ {w | P.HasIndex w i ∧ y ∈ P.projT w})} := by sorry

end OneOfManyCC
