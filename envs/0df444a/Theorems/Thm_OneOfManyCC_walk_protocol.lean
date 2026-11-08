-- Prove2me | Theorems.Thm_OneOfManyCC_walk_protocol
-- name    : OneOfManyCC.walk_protocol
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:55:41.880855+00:00
-- url     : https://prove2.me/theorems/243bcd1e-e1fc-4634-b21b-83c66d856333
-- title:
--   §5, proof of Theorem 1.2 — walking down $\Psi$ gives a protocol for $R$ of depth $\operatorname{depth}(\Psi)+\max\{\dots\}$
-- statement:
--   Let $R$ be a total relation on finite sets and $1\le k\le\min\{|A|,|B|\}$. Let $\Psi$ be a formula with AND and OR gates over solvable rectangles that is zero at every $x\in A$ and one at every $y\in B$. Then some protocol solving $R$ has depth at most
--
--   $$\operatorname{depth}(\Psi)+\max\{\mathrm{CC}(\mathrm{OneOut}^{\neq}_k(R)),\ \lceil\log_2|O|\rceil\}.$$
--
--   The players walk down $\Psi$ while the current subformula is zero at $x$ and one at $y$: at an AND gate Alice names a child that is zero at $x$, and at an OR gate Bob names a child that is one at $y$. At the leaf reached, $x\in A'$ and $y\in B'$, and they finish with a protocol solving $R$ on $A'\times B'$.
--
--   Differences from the source:
--   - encoding: depth $\max\{\dots\}+O(\log k+\log n)$ → the exact sum $\operatorname{depth}(\Psi)+\max\{\dots\}$; reason: the printed $O(\log k+\log n)$ is the depth of $\Psi$, stated in the item for $\Psi$; substituting gives the printed sentence
--   - encoding: leaves from $\mathcal F$, the functions of solvable rectangles → leaves typed as the solvable rectangles, valued by `rectFn`; reason: a rectangle is determined by its function
--   - encoding: $\log$ inside $O(\cdot)$ and $\lceil\log_2\cdot\rceil$ → `Real.logb 2` and `Nat.clog 2`; reason: the paper's logarithms are base 2; `Nat.clog 2 m` is $\lceil\log_2 m\rceil$ for $m\ge1$ and `Real.logb 2 0 = 0`
--   - encoding: finite sets $A, B, O$ → Fintype types in `Type`; reason: every finite set is equivalent to a type in `Type`, and this lets the statement quantify over all of them
--   - encoding: $\mathrm{Inj}_k(A)$ → the embeddings `Fin k ↪ A`; reason: injective maps from $k$ positions are exactly the $k$-tuples of pairwise distinct elements
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), §5, proof of Theorem 1.2, p.12

import Mathlib
import Definitions.Def_OneOfManyCC_Formula
import Definitions.Def_OneOfManyCC_rectFn

namespace OneOfManyCC

/-- **Walking down Ψ gives a protocol.**
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), §5, proof of Theorem 1.2, p.12:
"On inputs x ∈ A and y ∈ B, the players walk down Ψ from the root while the current subformula is
zero at x and one at y … At the leaf A′ × B′ they reach, x ∈ A′ and y ∈ B′, so they finish by running
a protocol of depth at most max{CC(OneOut≠ₖ(R)), ⌈log₂|O|⌉} that solves R on A′ × B′."

**Formalization Note.** The depth is the exact sum `Ψ.depth + max{…}`; the printed
`O(log k + log n)` term is `Ψ`'s depth bound, stated in `formula_psi`. -/
theorem walk_protocol {A B O : Type} [Fintype A] [Fintype B] [Fintype O]
    (R : A → B → O → Prop) (hR : IsTotal R) (k : ℕ) (hk₁ : 1 ≤ k)
    (hk : k ≤ min (Fintype.card A) (Fintype.card B)) (Ψ : Formula (SolvableRect k R))
    (hzero : ∀ x : A, Ψ.eval rectFn (Sum.inl x) = false)
    (hone : ∀ y : B, Ψ.eval rectFn (Sum.inr y) = true) :
    ∃ P : Protocol A B O, P.SolvesOn R Set.univ Set.univ ∧
      P.depth ≤ Ψ.depth + max (CC (OneOut k R)) (Nat.clog 2 (Fintype.card O)) := by sorry

end OneOfManyCC
