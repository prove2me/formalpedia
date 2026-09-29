-- Prove2me | Theorems.Thm_ModularCurve_gramMatrixOf_diffChar_marked_apply
-- name    : ModularCurve.gramMatrixOf_diffChar_marked_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/1dc66836-3c23-5623-8c9b-d4758229a076
-- title:
--   Gram matrix of difference characters at a marked point
-- statement:
--   Let $\iota$ be a finite type with decidable equality, let $e : \iota \to \mathbb{N}$ be a weight function, let $x_0 \in \iota$ be a marked element, and let $y, z$ be elements of the subtype $\{b : \iota \mid b \neq x_0\}$. Consider the equivalence `Equiv.optionSubtypeNe x₀` between $\mathrm{Option}\,\{b \mid b \neq x_0\}$ and $\iota$, which sends `none` to $x_0$ and `some b` to $b$. For each $b \neq x_0$, `diffChar` of this equivalence at $b$ is the element of `characterLattice ι` (the kernel of `degreeOn ι`, i.e. the sum-zero sublattice of $\iota \to \mathbb{Z}$) given by $x \mapsto [x = b] - [x = x_0]$, so $\delta_b - \delta_{x_0}$. The matrix `gramMatrixOf e (diffChar (Equiv.optionSubtypeNe x₀))`, whose $(i,j)$ entry is `gramMap e` (the restriction of the pairing `widthPairing e` to the character lattice) evaluated at the $i$-th and $j$-th of these vectors, is asserted to have $(y,z)$ entry equal to $\bigl(\text{if } y = z \text{ then } e(y) \text{ else } 0\bigr) + e(x_0)$ in $\mathbb{Z}$; that is, $e(y) + e(x_0)$ on the diagonal and $e(x_0)$ off it.
--
--   This is the explicit diagonal-plus-rank-one shape of the monodromy (width) pairing matrix in the difference basis $\{\delta_y - \delta_{x_0}\}_{y \neq x_0}$ of the character lattice, i.e. the reduced Laplacian of the weighted graph with weights $e$. It feeds the determinant computation behind [`ModularCurve.natCard_componentGroup_eq_kirchhoffCount`](thm.html#ModularCurve.natCard_componentGroup_eq_kirchhoffCount), where the matrix–determinant lemma turns it into the Kirchhoff count $\sum_x \prod_{y \neq x} e(y)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_gramMatrixOf_diffChar_marked_apply.lean

import Definitions.Def_ModularCurve_ComponentGroupKirchhoff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve Module
namespace ModularCurve
open Module
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem gramMatrixOf_diffChar_marked_apply (e : ι → ℕ) (x₀ : ι) (y z : {b : ι // b ≠ x₀}) :
    gramMatrixOf e (diffChar (Equiv.optionSubtypeNe x₀)) y z =
      (if y = z then (e y.1 : ℤ) else 0) + (e x₀ : ℤ) := by sorry
