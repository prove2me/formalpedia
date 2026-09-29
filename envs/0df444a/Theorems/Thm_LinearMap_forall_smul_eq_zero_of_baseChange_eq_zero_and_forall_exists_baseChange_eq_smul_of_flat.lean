-- Prove2me | Theorems.Thm_LinearMap_forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat
-- name    : LinearMap.forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/25b381b9-8ef2-5290-8352-17bddfd465c0
-- title:
--   Kernel and cokernel torsion bounds under flat base change
-- statement:
--   Let $R_0$ be a commutative ring, $R$ a commutative $R_0$-algebra that is flat as an $R_0$-module, and $M$, $N$ two $R_0$-modules. Let $u : M \to N$ be $R_0$-linear and let $J \subseteq R_0$ be an ideal. Assume two elementwise hypotheses: (i) for every $x \in M$ with $u(x) = 0$ and every $a \in J$ one has $a \cdot x = 0$, i.e. $J$ annihilates $\ker u$; and (ii) for every $y \in N$ and every $a \in J$ there exists $x \in M$ with $u(x) = a \cdot y$, i.e. $J N \subseteq \operatorname{im} u$. The conclusion is the conjunction of the corresponding two statements for the base-changed $R$-linear map $u_R =$ `u.baseChange R` on $R \otimes_{R_0} M \to R \otimes_{R_0} N$ and the ideal $J R =$ `J.map (algebraMap R₀ R)` of $R$: first, every $x \in R \otimes_{R_0} M$ with $u_R(x) = 0$ satisfies $a \cdot x = 0$ for all $a \in JR$; second, for every $y \in R \otimes_{R_0} N$ and every $a \in JR$ there is $x \in R \otimes_{R_0} M$ with $u_R(x) = a \cdot y$.
--
--   This is the statement that an annihilation bound on the kernel and a divisibility bound on the cokernel of an $R_0$-linear map persist after flat base change, with the ideal replaced by its extension. It is used in the project to transport such bounds along flat maps of base rings, notably in the verification that a map of quasi-coherent data becomes an isomorphism after base change and in a companion statement phrased via an isomorphism with a base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w w'

open TensorProduct

theorem LinearMap.forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat
    {R₀ : Type u} [CommRing R₀] {R : Type v} [CommRing R] [Algebra R₀ R] [Module.Flat R₀ R]
    {M : Type w} [AddCommGroup M] [Module R₀ M] {N : Type w'} [AddCommGroup N] [Module R₀ N]
    (u : M →ₗ[R₀] N) (J : Ideal R₀)
    (hk : ∀ x : M, u x = 0 → ∀ a ∈ J, a • x = 0)
    (hc : ∀ (y : N), ∀ a ∈ J, ∃ x : M, u x = a • y) :
    (∀ x : R ⊗[R₀] M, u.baseChange R x = 0 → ∀ a ∈ J.map (algebraMap R₀ R), a • x = 0) ∧
    (∀ (y : R ⊗[R₀] N), ∀ a ∈ J.map (algebraMap R₀ R), ∃ x : R ⊗[R₀] M, u.baseChange R x = a • y) := by sorry
