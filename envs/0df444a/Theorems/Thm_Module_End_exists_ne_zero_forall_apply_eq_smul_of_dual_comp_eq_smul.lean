-- Prove2me | Theorems.Thm_Module_End_exists_ne_zero_forall_apply_eq_smul_of_dual_comp_eq_smul
-- name    : Module.End.exists_ne_zero_forall_apply_eq_smul_of_dual_comp_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/76e0a04b-df55-5510-88f9-c8676eb8608b
-- title:
--   From a simultaneous dual eigenvector to a simultaneous eigenvector
-- statement:
--   Let $K$ be a field and $M$ a finite-dimensional $K$-vector space, let $R$ be a commutative ring, and let $T \colon R \to \operatorname{End}_K(M)$ and $a \colon R \to K$ be ring homomorphisms (so the operators $T(r)$ commute with one another, and $a$ is a $K$-valued character of $R$). Suppose $\mu \colon M \to K$ is a $K$-linear functional with $\mu \neq 0$ such that for every $r \in R$ the composite of $T(r)$ followed by $\mu$ equals $a(r) \cdot \mu$, i.e. $\mu(T(r)m) = a(r)\mu(m)$ for all $m \in M$. The conclusion is that there exists $m \in M$ with $m \neq 0$ and $T(r)m = a(r)m$ for every $r \in R$; that is, the simultaneous eigenvector condition for the character $a$, satisfied by $\mu$ in the dual module, is also satisfied by some non-zero vector of $M$ itself. Only the non-vanishing of the eigenvector is asserted: no relation between the dimensions of the eigenspace in $M$ and of the corresponding space of functionals is claimed.
--
--   This is the transfer of occurrence of a character of a commuting family of endomorphisms from the dual space to the space, used when an eigensystem is first located on a dual (or cohomological) realisation and an eigenvector in the original module is required. It is applied in the construction of a simultaneous eigenvector for the Hecke operators on the Tate module of the Jacobian of a modular curve of full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_End_exists_ne_zero_forall_apply_eq_smul_of_dual_comp_eq_smul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Module.End.exists_ne_zero_forall_apply_eq_smul_of_dual_comp_eq_smul
    {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    {R : Type*} [CommRing R] (T : R →+* Module.End K M) (a : R →+* K)
    (μ : Module.Dual K M) (hμ : μ ≠ 0) (hco : ∀ r : R, μ ∘ₗ (T r : M →ₗ[K] M) = a r • μ) :
    ∃ m : M, m ≠ 0 ∧ ∀ r : R, T r m = a r • m := by sorry
