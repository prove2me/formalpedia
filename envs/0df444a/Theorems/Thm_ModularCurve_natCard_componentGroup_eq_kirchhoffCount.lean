-- Prove2me | Theorems.Thm_ModularCurve_natCard_componentGroup_eq_kirchhoffCount
-- name    : ModularCurve.natCard_componentGroup_eq_kirchhoffCount
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/9c164b4e-e1ae-5808-89ee-5d06e34c8435
-- title:
--   Kirchhoff closed form for the component group order
-- statement:
--   Let $\iota$ be a finite, nonempty index type with decidable equality, and let $e : \iota \to \mathbb{N}$ be a family of widths with $e(x) > 0$ for every $x \in \iota$. Write $L =$ `characterLattice ι` for the sublattice of $\iota \to \mathbb{Z}$ given by the kernel of `degreeOn ι`, and let `gramMap e` $: L \to \operatorname{Hom}_{\mathbb{Z}}(L, \mathbb{Z})$ be the map obtained from the bilinear form `widthPairing e` by restricting both arguments to $L$. The group `componentGroup e` is by definition the quotient $\operatorname{Hom}_{\mathbb{Z}}(L,\mathbb{Z}) / \operatorname{range}(\mathtt{gramMap } e)$, i.e. the cokernel of this Gram map. The assertion is that the cardinality of this quotient, in the sense of `Nat.card`, equals $$\mathtt{kirchhoffCount } e \;=\; \sum_{x \in \iota} \ \prod_{y \neq x} e(y),$$ the sum over $x$ of the product of the widths at all indices other than $x$. Since the right-hand side is a positive natural number under the positivity hypothesis, the equality in particular records that the quotient is finite.
--
--   This is the matrix-tree (Kirchhoff) closed form for the order of the combinatorial component group attached to a family of widths: for unit widths it gives $\#\iota$, for two indices $e_0 + e_1$, and for three $e_0e_1 + e_0e_2 + e_1e_2$, the shape of Ribet's formulas for component groups of Jacobians of modular curves at a prime of multiplicative reduction. It is used for the finiteness statement [`ModularCurve.finite_componentGroup_of_pos`](thm.html#ModularCurve.finite_componentGroup_of_pos) and for the comparison with the Eisenstein numerator in [`ModularCurve.natCard_componentGroup_eq_eisensteinNumerator`](thm.html#ModularCurve.natCard_componentGroup_eq_eisensteinNumerator).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natCard_componentGroup_eq_kirchhoffCount.lean

import Definitions.Def_ModularCurve_ComponentGroupKirchhoff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
namespace ModularCurve
open Module
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {e : ι → ℕ}

theorem natCard_componentGroup_eq_kirchhoffCount [Nonempty ι] (he : ∀ x, 0 < e x) :
    Nat.card (componentGroup e) = kirchhoffCount e := by sorry
