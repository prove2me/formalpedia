-- Prove2me | Theorems.Thm_Module_End_exists_isNilpotent_pow_sub_one_of_mul_eq_pow_mul_of_isUnit
-- name    : Module.End.exists_isNilpotent_pow_sub_one_of_mul_eq_pow_mul_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/60af18bc-570e-5a37-a005-c70b6ec5e747
-- title:
--   An endomorphism conjugate to its q-th power is quasi-unipotent
-- statement:
--   Let $F$ be a field and $V$ a finite-dimensional $F$-vector space. Let $g, h \colon V \to V$ be $F$-linear endomorphisms, each assumed to be a unit in the endomorphism ring $\mathrm{End}_F(V)$ (that is, invertible), and let $q$ be a natural number with $2 \le q$. Assume the relation $h g = g^q h$ in $\mathrm{End}_F(V)$, equivalently $h g h^{-1} = g^q$. The conclusion is that there exists a natural number $e$ with $0 < e$ such that $g^e - 1$ is nilpotent, i.e. $(g^e - 1)^n = 0$ for some $n$; in other words $g$ is quasi-unipotent. No separability, characteristic or algebraic closedness assumption is placed on $F$, and the hypothesis that $h$ is invertible is used only through the conjugation relation.
--
--   This is the linear-algebra core of Grothendieck's $\ell$-adic monodromy theorem: a Frobenius lift conjugates a generator of tame inertia to its $q$-th power, and the conclusion is that inertia acts quasi-unipotently. It is cited in the project by the two statements on the action of the inertia subgroup on torsion points under a hypothesis of invertibility on $p$-adic tensor products of quaternionic orders.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_End_exists_isNilpotent_pow_sub_one_of_mul_eq_pow_mul_of_isUnit.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Module.End.exists_isNilpotent_pow_sub_one_of_mul_eq_pow_mul_of_isUnit
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (g h : Module.End F V) (hg : IsUnit g) (hh : IsUnit h) {q : ℕ} (hq : 2 ≤ q)
    (hrel : h * g = g ^ q * h) :
    ∃ e : ℕ, 0 < e ∧ IsNilpotent (g ^ e - 1) := by sorry
