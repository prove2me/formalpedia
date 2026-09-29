-- Prove2me | Theorems.Thm_Module_End_eq_zero_of_isNilpotent_of_forall_commute_of_forall_isUnit_of_finrank_eq
-- name    : Module.End.eq_zero_of_isNilpotent_of_forall_commute_of_forall_isUnit_of_finrank_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/d855ef5d-54a3-5655-ae67-9c64360ba051
-- title:
--   Nilpotent endomorphisms commuting with a division algebra vanish
-- statement:
--   Let $F$ be a field and $V$ a finite-dimensional $F$-vector space, and let $D$ be a ring equipped with an $F$-algebra structure such that every non-zero element of $D$ is a unit (so $D$ is a, possibly non-commutative, division algebra over $F$). Let $\iota \colon D \to \operatorname{End}_F(V)$ be a homomorphism of $F$-algebras, and assume the equality of dimensions $\dim_F D = \dim_F V$ (as `Module.finrank`, hence in $\mathbb{N}$). Let $N$ be an $F$-linear endomorphism of $V$ that commutes with $\iota(d)$ for every $d \in D$, and suppose $N$ is nilpotent, i.e. $N^k = 0$ for some $k \in \mathbb{N}$. The conclusion is that $N = 0$. No injectivity or non-degeneracy is assumed of $\iota$, and $D$ is not assumed non-trivial; these follow from the hypotheses once $V \neq 0$, while for $V = 0$ the conclusion is vacuous.
--
--   This is the nilpotent case of Schur's lemma in the form used for the commutant of a division algebra of operators: since $V$ is free of rank one over $D$, the commutant of $\iota(D)$ in $\operatorname{End}_F(V)$ is again a division algebra and so contains no non-zero nilpotents. It is used to show that an endomorphism commuting with such a $D$ whose $(p-1)$-st power minus one is nilpotent is in fact of finite order, via [`Module.End.pow_eq_one_of_isNilpotent_pow_sub_one_of_forall_commute_of_forall_isUnit_of_finrank_eq`](thm.html#Module.End.pow_eq_one_of_isNilpotent_pow_sub_one_of_forall_commute_of_forall_isUnit_of_finrank_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_End_eq_zero_of_isNilpotent_of_forall_commute_of_forall_isUnit_of_finrank_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Module.End.eq_zero_of_isNilpotent_of_forall_commute_of_forall_isUnit_of_finrank_eq
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {D : Type*} [Ring D] [Algebra F D] (hD : ∀ x : D, x ≠ 0 → IsUnit x)
    (ι : D →ₐ[F] Module.End F V) (hdim : Module.finrank F D = Module.finrank F V)
    {N : Module.End F V} (hcomm : ∀ d : D, Commute (ι d) N) (hN : IsNilpotent N) : N = 0 := by sorry
