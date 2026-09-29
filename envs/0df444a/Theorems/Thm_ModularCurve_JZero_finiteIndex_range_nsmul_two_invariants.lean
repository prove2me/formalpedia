-- Prove2me | Theorems.Thm_ModularCurve_JZero_finiteIndex_range_nsmul_two_invariants
-- name    : ModularCurve.JZero.finiteIndex_range_nsmul_two_invariants
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/dfaa4598-fda6-50d2-93af-0a6441a7518a
-- title:
--   Weak Mordell–Weil at 2 for J₀(N)
-- statement:
--   Let $N$ be a nonzero natural number and let $K$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ that is finite-dimensional over $\mathbb{Q}$. Write $F_N$ for the subfield `modularFunctionFieldBar N` of $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ obtained by adjoining to $\overline{\mathbb{Q}}$ the image, under the coefficientwise embedding, of the field `modularFunctionFieldFull N` generated over $\mathbb{Q}$ inside $\mathrm{LaurentSeries}(\mathbb{Q})$ by the divisor expansions of level $N$; and let `JZero N` be $\mathrm{Pic}^0$ of $F_N$ over $\overline{\mathbb{Q}}$, namely the group of finitely supported $\mathbb{Z}$-valued functions on the places of $F_N$ over $\overline{\mathbb{Q}}$ of total degree zero, modulo the principal divisors. This group carries an action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, and for a subgroup $H$ the notation $\cdot\,^+ H$ denotes the subgroup of $H$-invariants. Assume that every element of `JZero N` killed by $2$ is fixed by the fixing subgroup of $K$, i.e. the full $2$-torsion is $K$-rational. Then the range of the endomorphism "multiplication by $2$" of the group of invariants of `JZero N` under the fixing subgroup of $K$ has finite index in that group; equivalently, $J_0(N)(K)/2J_0(N)(K)$ is finite.
--
--   This is the weak Mordell–Weil theorem at $n = 2$ for the Jacobian of $X_0(N)$, in the form with the $2$-torsion assumed rational over the base field $K$. It feeds the descent arguments [`ModularCurve.JZero.exists_descent_height_two_invariants_of_prime_of_five_le`](thm.html#ModularCurve.JZero.exists_descent_height_two_invariants_of_prime_of_five_le) and [`ModularCurve.JZero.addGroup_fg_invariants_of_prime_of_five_le`](thm.html#ModularCurve.JZero.addGroup_fg_invariants_of_prime_of_five_le), which deduce finite generation of the group of $K$-points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_finiteIndex_range_nsmul_two_invariants.lean

import Definitions.Def_ModularCurve_ArithmeticGalois
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Index
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.JZero.finiteIndex_range_nsmul_two_invariants (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (h2 : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) 2 ≤ JZero N ^+ ↥K.fixingSubgroup) :
    (nsmulAddMonoidHom 2 : ↥(JZero N ^+ ↥K.fixingSubgroup) →+ ↥(JZero N ^+ ↥K.fixingSubgroup)).range.FiniteIndex := by sorry
