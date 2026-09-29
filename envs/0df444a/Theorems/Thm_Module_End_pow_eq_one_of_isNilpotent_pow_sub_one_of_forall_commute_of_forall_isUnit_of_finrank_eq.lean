-- Prove2me | Theorems.Thm_Module_End_pow_eq_one_of_isNilpotent_pow_sub_one_of_forall_commute_of_forall_isUnit_of_finrank_eq
-- name    : Module.End.pow_eq_one_of_isNilpotent_pow_sub_one_of_forall_commute_of_forall_isUnit_of_finrank_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/2b92040e-c113-563a-8c81-b181301072c6
-- title:
--   Quasi-unipotent operator commuting with a division algebra has g^e=1
-- statement:
--   Let $F$ be a field and $V$ a finite-dimensional $F$-vector space. Let $D$ be a ring equipped with an $F$-algebra structure such that every non-zero element of $D$ is a unit, and let $\iota : D \to \operatorname{End}_F(V)$ be a homomorphism of $F$-algebras. Assume $\dim_F D = \dim_F V$, the dimensions being taken as `Module.finrank`. Let $g$ be an $F$-linear endomorphism of $V$ that commutes with $\iota(d)$ for every $d \in D$, and let $e$ be a natural number such that $g^e - 1$ is nilpotent in $\operatorname{End}_F(V)$, i.e. some power of $g^e - 1$ vanishes. The conclusion is that $g^e = 1$, that is, $g^e$ is the identity endomorphism of $V$.
--
--   This is the rigidity statement that an endomorphism commuting with the action of a division algebra of operators of the same dimension as the module, and which is quasi-unipotent in the sense that $g^e-1$ is nilpotent, already satisfies $g^e = 1$. It is used in the analysis of inertia acting on torsion of abelian varieties with quaternionic multiplication, where $V$ is a Tate module and $D$ a quaternion algebra that is a division algebra over the relevant local field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_End_pow_eq_one_of_isNilpotent_pow_sub_one_of_forall_commute_of_forall_isUnit_of_finrank_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Module.End.pow_eq_one_of_isNilpotent_pow_sub_one_of_forall_commute_of_forall_isUnit_of_finrank_eq
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {D : Type*} [Ring D] [Algebra F D] (hD : ∀ x : D, x ≠ 0 → IsUnit x)
    (ι : D →ₐ[F] Module.End F V) (hdim : Module.finrank F D = Module.finrank F V)
    {g : Module.End F V} (hcomm : ∀ d : D, Commute (ι d) g) {e : ℕ}
    (he : IsNilpotent (g ^ e - 1)) : g ^ e = 1 := by sorry
