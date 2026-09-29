-- Prove2me | Theorems.Thm_Module_Finite_exists_trace_end_eq_sum_dual_apply_of_projective
-- name    : Module.Finite.exists_trace_end_eq_sum_dual_apply_of_projective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/5d2980a9-ec70-58f2-872e-1d21feac9c2d
-- title:
--   Trace via dual families on finitely generated projective modules
-- statement:
--   Let $A$ be a commutative ring and $M$ an $A$-module which is both finitely generated and projective (the module structure on an additive commutative group $M$, with the finiteness and projectivity hypotheses, is assumed as typeclass data). The assertion is the existence of an $A$-linear map $\tau \colon \operatorname{End}_A(M) \to A$ on the module of $A$-linear endomorphisms of $M$ with the following universal property: for every natural number $n$, every family $x \colon \mathrm{Fin}\,n \to M$ of elements of $M$ and every family $\varphi \colon \mathrm{Fin}\,n \to \operatorname{Hom}_A(M,A)$ of $A$-linear functionals such that $\sum_{i} \varphi_i(m)\, x_i = m$ for all $m \in M$, and for every $A$-linear endomorphism $f$ of $M$, one has $\tau(f) = \sum_i \varphi_i(f(x_i))$. Thus $\tau$ is a single linear functional computing, simultaneously for all finite dual families indexed by $\mathrm{Fin}\,n$, the familiar expression $\sum_i \varphi_i(f x_i)$; in particular the statement contains the independence of that sum from the chosen dual family. No basis of $M$ is assumed, and $\tau$ is not asserted to coincide with any previously defined trace map.
--
--   This is the trace of an endomorphism of a finitely generated projective module, in the form of a linear functional on $\operatorname{End}_A(M)$ computed by any finite dual family; unlike Mathlib's `LinearMap.trace`, which is defined through a finite basis, it is available for projective modules that need not be free. It is used in the construction of retractions for pushforwards of unit modules on affine schemes, in [`AlgebraicGeometry.OModulePresheaf.exists_affHom_pushforwardUnit_unit_retraction_of_finrank_eq_of_isUnit`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_affHom_pushforwardUnit_unit_retraction_of_finrank_eq_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Finite_exists_trace_end_eq_sum_dual_apply_of_projective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open scoped BigOperators

theorem Module.Finite.exists_trace_end_eq_sum_dual_apply_of_projective
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Projective A M] :
    ∃ τ : (M →ₗ[A] M) →ₗ[A] A,
      ∀ (n : ℕ) (x : Fin n → M) (φ : Fin n → (M →ₗ[A] A)),
        (∀ m : M, ∑ i, φ i m • x i = m) →
          ∀ f : M →ₗ[A] M, τ f = ∑ i, φ i (f (x i)) := by sorry
