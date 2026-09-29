-- Prove2me | Theorems.Thm_LinearMap_BilinForm_orthogonal_le_sup_of_restrict_nondegenerate_of_forall_sub_mem_sup
-- name    : LinearMap.BilinForm.orthogonal_le_sup_of_restrict_nondegenerate_of_forall_sub_mem_sup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/9c5290e6-bc68-56e5-9756-b0ea19cbe378
-- title:
--   Orthogonal of the toric part lies in toric + old
-- statement:
--   Let $K$ be a field and $V$ a finite-dimensional $K$-vector space, let $\rho$ be a representation of a group $\Gamma$ on $V$ (a monoid homomorphism from $\Gamma$ to the $K$-linear endomorphisms of $V$), let $\chi\colon\Gamma\to K^{\times}$ be a group homomorphism and $I\le\Gamma$ a subgroup. Let $e$ be a $K$-bilinear form on $V$ which is reflexive ($e(a,b)=0$ implies $e(b,a)=0$), has no nonzero vector orthogonal to all of $V$ on the left, and satisfies $e(\rho(\gamma)a,\rho(\gamma)b)=\chi(\gamma)\,e(a,b)$ for all $\gamma\in\Gamma$ and all $a,b\in V$. Let $V^t,V^o\le V$ be subspaces, each stable under $\rho(\gamma)$ for every $\gamma\in I$, such that $e(x,y)=0$ for all $x\in V^t$, $y\in V^o$; such that $\rho(\tau)v-v\in V^t+V^o$ for every $\tau\in I$ and every $v\in V$; such that any $y\in V^o$ with $e(y,y')=0$ for all $y'\in V^o$ vanishes; and such that $\chi(\tau_0)\ne 1$ for some $\tau_0\in I$. Then every $v\in V$ with $e(x,v)=0$ for all $x\in V^t$ lies in $V^t+V^o$.
--
--   This is the linear-algebra core of Grothendieck's orthogonality relation at the residue characteristic, in the shape used for the $\ell$-adic Tate module of the Jacobian of a semistable curve: $V^t$ the toric part, $V^o$ the part of good reduction, $I$ an inertia subgroup acting trivially on $V/(V^t+V^o)$, and $\chi$ the cyclotomic character. It is used in the proof of [`PadicInt.exists_pow_smul_mem_sup_of_forall_bilinForm_apply_eq_zero`](thm.html#PadicInt.exists_pow_smul_mem_sup_of_forall_bilinForm_apply_eq_zero), the integral counterpart of the same statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_BilinForm_orthogonal_le_sup_of_restrict_nondegenerate_of_forall_sub_mem_sup.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LinearMap.BilinForm.orthogonal_le_sup_of_restrict_nondegenerate_of_forall_sub_mem_sup
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Γ : Type*} [Group Γ] (ρ : Representation K Γ V) (χ : Γ →* Kˣ)
    (I : Subgroup Γ)
    (e : LinearMap.BilinForm K V)
    (hrefl : ∀ a b : V, e a b = 0 → e b a = 0)
    (hnondeg : ∀ a : V, (∀ b : V, e a b = 0) → a = 0)
    (hequiv : ∀ (γ : Γ) (a b : V), e (ρ γ a) (ρ γ b) = ((χ γ : Kˣ) : K) * e a b)
    (Vt Vo : Submodule K V)
    (hVt : ∀ γ ∈ I, ∀ x ∈ Vt, ρ γ x ∈ Vt)
    (hVo : ∀ γ ∈ I, ∀ y ∈ Vo, ρ γ y ∈ Vo)
    (hISO : ∀ x ∈ Vt, ∀ y ∈ Vo, e x y = 0)
    (hCUT : ∀ τ ∈ I, ∀ v : V, ρ τ v - v ∈ Vt ⊔ Vo)
    (hOLD : ∀ y ∈ Vo, (∀ y' ∈ Vo, e y y' = 0) → y = 0)
    (hCYC : ∃ τ₀ ∈ I, χ τ₀ ≠ 1) :
    e.orthogonal Vt ≤ Vt ⊔ Vo := by sorry
