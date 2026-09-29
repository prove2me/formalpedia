-- Prove2me | Theorems.Thm_Module_sum_dual_apply_eq_natCast_of_rankAtStalk_eq
-- name    : Module.sum_dual_apply_eq_natCast_of_rankAtStalk_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/8b77ff07-b1ae-552b-937f-ccf9307567b7
-- title:
--   Dual family trace equals the constant stalk rank
-- statement:
--   Let $A$ be a commutative ring and $M$ an $A$-module (an additive commutative group with an $A$-module structure). Let $n$ be a natural number, and let $x : \mathrm{Fin}\,n \to M$ and $\varphi : \mathrm{Fin}\,n \to (M \to_{A} A)$ be families of elements and of $A$-linear functionals forming a dual family in the sense that $\sum_{i} \varphi_i(m) \cdot x_i = m$ for every $m \in M$. Let $d$ be a natural number and assume that for every prime $\mathfrak p$ in the prime spectrum of $A$ one has $\mathrm{Module.rankAtStalk}\,M\,\mathfrak p = d$, i.e. the rank of the localisation $M_{\mathfrak p}$ over $A_{\mathfrak p}$ is $d$ at every prime. The conclusion is the identity $\sum_{i} \varphi_i(x_i) = d$ in $A$, the right-hand side being the image of $d$ under the canonical map $\mathbb N \to A$. No finiteness, projectivity or freeness hypothesis on $M$ is imposed: the dual family already exhibits $M$ as a retract of $A^n$.
--
--   This is the statement that for a finitely generated projective module presented by a dual basis, the trace of the identity endomorphism — computed as $\sum_i \varphi_i(x_i)$ — equals the rank, under the hypothesis that the rank is the same constant $d$ at every prime of the base. It is used in the construction of retractions of pushforward units for presheaves of modules, via [`AlgebraicGeometry.OModulePresheaf.exists_affHom_pushforwardUnit_unit_retraction_of_finrank_eq_of_isUnit`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_affHom_pushforwardUnit_unit_retraction_of_finrank_eq_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_sum_dual_apply_eq_natCast_of_rankAtStalk_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open scoped BigOperators

theorem Module.sum_dual_apply_eq_natCast_of_rankAtStalk_eq
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    {n : ℕ} (x : Fin n → M) (φ : Fin n → (M →ₗ[A] A)) (hxφ : ∀ m : M, ∑ i, φ i m • x i = m)
    (d : ℕ) (hd : ∀ p : PrimeSpectrum A, Module.rankAtStalk M p = d) :
    ∑ i, φ i (x i) = (d : A) := by sorry
