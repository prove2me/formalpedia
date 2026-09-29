-- Prove2me | Theorems.Thm_ModularCurve_componentGroup_subsingleton
-- name    : ModularCurve.componentGroup_subsingleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/c99f9a70-3ac4-5448-a6a2-39a5dbc3d29b
-- title:
--   Vanishing component group for at most one edge
-- statement:
--   Let $\iota$ be a finite type with $\#\iota \le 1$, and let $e : \iota \to \mathbb{N}$ be arbitrary. Recall the $\mathbb{Z}$-module $\iota \to \mathbb{Z}$, its submodule `characterLattice ι` defined as the kernel of the map `degreeOn ι`, and the homomorphism `gramMap e` from `characterLattice ι` to its $\mathbb{Z}$-linear dual obtained by restricting the pairing `widthPairing e` in both arguments to `characterLattice ι`; the group `componentGroup e` is by definition the quotient of $\operatorname{Hom}_{\mathbb{Z}}(\mathtt{characterLattice}\ \iota, \mathbb{Z})$ by the image of `gramMap e`. The theorem asserts that under the hypothesis $\#\iota \le 1$ this quotient is a subsingleton, i.e. any two of its elements are equal, so `componentGroup e` is trivial. The statement is for an index type of cardinality at most one, with no positivity or other condition imposed on the function $e$.
--
--   In the combinatorial model of the component group of the Jacobian of a modular curve at a prime of multiplicative reduction, $\iota$ indexes the singular points of the dual graph and $e$ their widths; the assertion is the degenerate case in which the graph has at most one edge, so that its first homology, and hence the component group, vanishes. It is used by [`ModularCurve.finite_componentGroup_of_pos`](thm.html#ModularCurve.finite_componentGroup_of_pos) as the base case in the finiteness statement for these component groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_componentGroup_subsingleton.lean

import Definitions.Def_ModularCurve_ComponentGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
namespace ModularCurve
variable {ι : Type*} [Fintype ι]

theorem componentGroup_subsingleton (hι : Fintype.card ι ≤ 1) (e : ι → ℕ) :
    Subsingleton (componentGroup e) := by sorry
