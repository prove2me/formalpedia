-- Prove2me | Theorems.Thm_GL2F3_isConj_pow_three_of_orderOf_eq_eight
-- name    : GL2F3.isConj_pow_three_of_orderOf_eq_eight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/414f2b7d-af10-52bd-adf4-5291a378fe5a
-- title:
--   Order-8 elements of GL₂(mathbb F₃) are conjugate to their cubes
-- statement:
--   Let $g$ be an element of the general linear group $\mathrm{GL}_2(\mathbb Z/3)$, i.e. of the unit group of $2\times 2$ matrices over $\mathbb Z/3$, and suppose that the order of $g$ in this group is exactly $8$. The conclusion is that $g$ and $g^3$ are conjugate in $\mathrm{GL}_2(\mathbb Z/3)$: there exists $c$ in the group with $c g = g^{3} c$, equivalently $c g c^{-1} = g^{3}$. No further hypotheses are imposed; the statement is purely group-theoretic about the finite group $\mathrm{GL}_2(\mathbb F_3)$, whose elements of order $8$ are exactly the generators of its non-split Cartan subgroups.
--
--   This records one half of the description of the two conjugacy classes of elements of order $8$ in $\mathrm{GL}_2(\mathbb F_3)$ (the complementary negative statement being that $g$ is not conjugate to $g^{5}$). It feeds the construction of a Galois extension with prescribed inertia and Frobenius behaviour used in the Langlands–Tunnell input to the argument, via [`LanglandsTunnell.exists_inertia_eq_bot_isArithFrobAt_orderOf_eq_eight`](thm.html#LanglandsTunnell.exists_inertia_eq_bot_isArithFrobAt_orderOf_eq_eight).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GL2F3_isConj_pow_three_of_orderOf_eq_eight.lean

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Conj

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GL2F3.isConj_pow_three_of_orderOf_eq_eight (g : GL (Fin 2) (ZMod 3))
    (hg : orderOf g = 8) : IsConj g (g ^ 3) := by sorry
