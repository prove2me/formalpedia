-- Prove2me | Theorems.Thm_NumberField_finrank_cyclotomicField_three_eq_one_of_forall_isUnramifiedAt
-- name    : NumberField.finrank_cyclotomicField_three_eq_one_of_forall_isUnramifiedAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/14c3c510-4b0b-5937-bdc8-3d9785ed6e1e
-- title:
--   ℚ(ζ₃) has no unramified nontrivial extension
-- statement:
--   Let $F$ be a number field (a field of characteristic zero, finite-dimensional over $\mathbb{Q}$) carrying an algebra structure over `CyclotomicField 3 ℚ`, the cyclotomic field $\mathbb{Q}(\zeta_3)$ as constructed in Mathlib. Write $\mathcal{O}_F$ and $\mathcal{O}_{\mathbb{Q}(\zeta_3)}$ for the respective rings of integers. Assume that for every maximal ideal $P$ of $\mathcal{O}_F$ the algebra $\mathcal{O}_{\mathbb{Q}(\zeta_3)} \to \mathcal{O}_F$ is unramified at $P$ in the sense of `Algebra.IsUnramifiedAt`, i.e. the localisation of $\mathcal{O}_F$ at $P$ is formally unramified over $\mathcal{O}_{\mathbb{Q}(\zeta_3)}$. The conclusion is that the dimension of $F$ as a vector space over $\mathbb{Q}(\zeta_3)$ equals $1$; equivalently, $F$ is no larger than its base $\mathbb{Q}(\zeta_3)$. Note that no compatibility between the given $\mathbb{Q}(\zeta_3)$-algebra structure and the $\mathbb{Q}$-algebra structures is assumed: it is automatic, since any ring homomorphism out of $\mathbb{Q}$ into a field of characteristic zero is unique.
--
--   This is the Minkowski-type statement that $\mathbb{Q}(\zeta_3)$, having absolute discriminant $3$ and class number one, admits no nontrivial finite extension unramified at all finite primes. It feeds the inertia-stabiliser computation [`NumberField.stabilizer_primitiveRoot_three_le_of_forall_inertia_inf_le`](thm.html#NumberField.stabilizer_primitiveRoot_three_le_of_forall_inertia_inf_le), which in turn serves the $p = 3$ input of the relevant vanishing statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_finrank_cyclotomicField_three_eq_one_of_forall_isUnramifiedAt.lean

import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.Cyclotomic.Discriminant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped NumberField

theorem NumberField.finrank_cyclotomicField_three_eq_one_of_forall_isUnramifiedAt
    {F : Type*} [Field F] [NumberField F] [Algebra (CyclotomicField 3 ℚ) F]
    (h : ∀ (P : Ideal (𝓞 F)) (_ : P.IsMaximal),
      Algebra.IsUnramifiedAt (𝓞 (CyclotomicField 3 ℚ)) P) :
    Module.finrank (CyclotomicField 3 ℚ) F = 1 := by sorry
