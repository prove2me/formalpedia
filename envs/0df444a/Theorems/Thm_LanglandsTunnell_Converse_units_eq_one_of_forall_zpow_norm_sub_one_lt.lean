-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_units_eq_one_of_forall_zpow_norm_sub_one_lt
-- name    : LanglandsTunnell.Converse.units_eq_one_of_forall_zpow_norm_sub_one_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/e8ef9d02-6bbb-51d8-95f0-96d884c2ce7c
-- title:
--   No small subgroups in ℂ^×
-- statement:
--   Let $z$ be a unit of the field $\mathbb{C}$, that is an element of $\mathbb{C}^\times$, and suppose that for every integer $n$ (negative exponents included) the complex number underlying the unit $z^n$ satisfies $\|z^n - 1\| < 1$, where $\|\cdot\|$ is the usual absolute value on $\mathbb{C}$. The conclusion is that $z$ is the identity unit $1$. Thus the only element of $\mathbb{C}^\times$ whose full cyclic subgroup $\{z^n : n \in \mathbb{Z}\}$ is contained in the open disc of radius $1$ about $1$ is $z = 1$; equivalently, $\mathbb{C}^\times$ has no nontrivial subgroup inside that neighbourhood of the identity. The use of all integer exponents is essential for the statement as phrased: for $z = 1/2$ one has $\|z^n - 1\| < 1$ for every natural number $n$, while the hypothesis fails at $n = -1$.
--
--   This is the 'no small subgroups' property of $\mathbb{C}^\times$, specialised to the neighbourhood of $1$ given by the open unit disc centred at $1$. It is used in the construction of conductor exponents for continuous characters, being cited by [`LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous`](thm.html#LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous), where it forces a continuous homomorphism with small image to be trivial on a suitable open subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_units_eq_one_of_forall_zpow_norm_sub_one_lt.lean

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.Converse.units_eq_one_of_forall_zpow_norm_sub_one_lt
    (z : ℂˣ)
    (hz : ∀ n : ℤ, ‖((z ^ n : ℂˣ) : ℂ) - 1‖ < 1) : z = 1 := by sorry
