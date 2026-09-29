-- Prove2me | Theorems.Thm_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne
-- name    : IsIrreducible.topologicalKrullDim_add_one_le_of_isClosed_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/7d6ee144-8a99-5238-bd43-3cbcac119e07
-- title:
--   Dimension drop for a proper closed subset of an irreducible set
-- statement:
--   Let $X$ be a topological space, and let $Y, Z \subseteq X$ be subsets, each regarded as a topological space with the subspace topology. Assume $Z$ is irreducible (non-empty, and not the union of two proper relatively closed subsets), that $Y$ is closed in $X$, that $Y \subseteq Z$, and that $Y \neq Z$. Then $$\operatorname{topologicalKrullDim} Y + 1 \le \operatorname{topologicalKrullDim} Z,$$ where `topologicalKrullDim` of a space is the Krull dimension of its lattice of irreducible closed subsets, that is, the supremum of the lengths $n$ of chains $T_0 \subsetneq T_1 \subsetneq \cdots \subsetneq T_n$ of non-empty irreducible closed subsets, taken in $\{-\infty\} \cup \mathbb{N} \cup \{+\infty\}$. In particular, the inequality holds vacuously in the degenerate case $Y = \emptyset$, where the left-hand side is $-\infty$, and it forces $\operatorname{topologicalKrullDim} Z = +\infty$ whenever $Y$ has infinite dimension; when $\operatorname{topologicalKrullDim} Z$ is finite and equal to $d+1$, every closed subset of $X$ contained in $Z$ and distinct from $Z$ has dimension at most $d$.
--
--   This is the standard dimension drop for topological (combinatorial) Krull dimension, as in the usual treatments of dimension theory of schemes. It is the inductive step used in arguments that induct on the dimension of the support of a coherent sheaf, and is cited in this development by the results on the polynomiality of Euler characteristics $n \mapsto \chi(\mathcal{F} \otimes \mathcal{L}^{\otimes n})$ (Snapper's theorem) and the identification of the leading coefficient with the rank at a stalk.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem IsIrreducible.topologicalKrullDim_add_one_le_of_isClosed_of_ne
    {X : Type u} [TopologicalSpace X] {Y Z : Set X}
    (hZ : IsIrreducible Z) (hY : IsClosed Y) (hYZ : Y ⊆ Z) (hne : Y ≠ Z) :
    topologicalKrullDim Y + 1 ≤ topologicalKrullDim Z := by sorry
