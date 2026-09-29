-- Prove2me | Theorems.Thm_Module_exists_basis_forall_semilinear_apply_eq_of_isGalois
-- name    : Module.exists_basis_forall_semilinear_apply_eq_of_isGalois
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/0ce49b14-1e01-5ae6-8ee1-3e6dcdee0ddf
-- title:
--   Galois descent: a semilinear action with open stabilisers has a fixed basis
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra which is Galois over $K$ (no finiteness of $L/K$ is assumed), and let $V$ be an additive group with an $L$-module structure which is finite-dimensional over $L$. Suppose given a map $\rho$ assigning to each $K$-algebra automorphism $\sigma$ of $L$ an additive endomorphism $\rho(\sigma)$ of $V$, subject to: semilinearity, $\rho(\sigma)(a \cdot v) = \sigma(a) \cdot \rho(\sigma)(v)$ for all $\sigma$, all $a \in L$ and all $v \in V$; $\rho(1)$ is the identity on $V$; and $\rho(\sigma\tau) = \rho(\sigma) \circ \rho(\tau)$ for all $\sigma, \tau$. Suppose moreover that stabilisers are open in the following sense: for every $v \in V$ there is an intermediate field $E$ of $L/K$, finite-dimensional over $K$, such that every $\sigma$ in the fixing subgroup of $E$ (i.e. fixing $E$ pointwise) satisfies $\rho(\sigma)(v) = v$. The conclusion is that there exists an $L$-basis $b$ of $V$ indexed by $\mathrm{Fin}(\dim_L V)$ with $\rho(\sigma)(b_i) = b_i$ for every index $i$ and every $\sigma$.
--
--   This is Galois descent for finite-dimensional vector spaces, the vanishing of $H^1(\mathrm{Gal}(L/K), \mathrm{GL}_n(L))$ in the form due to Speiser ("Hilbert 90 for $\mathrm{GL}_n$"), stated for a possibly infinite Galois extension under the hypothesis that every vector has open stabiliser; it rests on the finite-degree case, in which the fully fixed vectors span $V$ over $L$ ([`Submodule.span_fixedPoints_semilinear_eq_top`](thm.html#Submodule.span_fixedPoints_semilinear_eq_top)). It is used to descend Riemann–Roch spaces on modular curves along the action of the arithmetic Galois group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_exists_basis_forall_semilinear_apply_eq_of_isGalois.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem Module.exists_basis_forall_semilinear_apply_eq_of_isGalois
    (K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (V : Type*) [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (ρ : (L ≃ₐ[K] L) → V →+ V)
    (hρ_smul : ∀ (σ : L ≃ₐ[K] L) (a : L) (v : V), ρ σ (a • v) = σ a • ρ σ v)
    (hρ_one : ∀ v : V, ρ 1 v = v)
    (hρ_mul : ∀ (σ τ : L ≃ₐ[K] L) (v : V), ρ (σ * τ) v = ρ σ (ρ τ v))
    (hopen : ∀ v : V, ∃ E : IntermediateField K L, FiniteDimensional K E ∧
      ∀ σ : L ≃ₐ[K] L, σ ∈ E.fixingSubgroup → ρ σ v = v) :
    ∃ b : Module.Basis (Fin (Module.finrank L V)) L V, ∀ (i : Fin (Module.finrank L V)) (σ : L ≃ₐ[K] L),
      ρ σ (b i) = b i := by sorry
