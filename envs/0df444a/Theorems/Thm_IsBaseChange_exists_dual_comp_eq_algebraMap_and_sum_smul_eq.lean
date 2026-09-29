-- Prove2me | Theorems.Thm_IsBaseChange_exists_dual_comp_eq_algebraMap_and_sum_smul_eq
-- name    : IsBaseChange.exists_dual_comp_eq_algebraMap_and_sum_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/56e7595d-c5e6-5689-bc6f-474b0ee04e92
-- title:
--   Dual families extend along a base change
-- statement:
--   Let $A$ and $A'$ be commutative rings with $A'$ an $A$-algebra, let $M$ be an $A$-module, and let $M'$ be an abelian group carrying compatible $A$- and $A'$-module structures (a scalar tower over $A \to A'$). Let $f \colon M \to M'$ be $A$-linear and assume `IsBaseChange A' f`, i.e. $f$ exhibits $M'$ as the base change $A' \otimes_A M$: the induced $A'$-linear map $A' \otimes_A M \to M'$ is an isomorphism. Let $n$ be a natural number and suppose given $x \colon \mathrm{Fin}\,n \to M$ and $A$-linear forms $\varphi_i \colon M \to A$ for $i \in \mathrm{Fin}\,n$ such that $\sum_i \varphi_i(m)\, x_i = m$ for every $m \in M$. The conclusion is that there exist $A'$-linear forms $\varphi'_i \colon M' \to A'$, $i \in \mathrm{Fin}\,n$, such that $\varphi'_i(f(m)) = \mathrm{algebraMap}_{A,A'}(\varphi_i(m))$ for all $i$ and all $m \in M$, and such that $\sum_i \varphi'_i(m')\, f(x_i) = m'$ for every $m' \in M'$. Thus the pairs $(f(x_i), \varphi'_i)$ form a dual family for $M'$ over $A'$ of the same length $n$.
--
--   This is the statement that a finite dual (or coordinate) family for a module is carried to one for its base change, the forms being the $A'$-linear extensions of the original ones; it underlies the compatibility of the associated dual-family trace with base change. It is used in the treatment of locally free modules of given rank at stalks and of retractions for pushforwards of module presheaves on affine schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsBaseChange_exists_dual_comp_eq_algebraMap_and_sum_smul_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w w'

open scoped BigOperators

theorem IsBaseChange.exists_dual_comp_eq_algebraMap_and_sum_smul_eq
    {A : Type u} [CommRing A] {A' : Type v} [CommRing A'] [Algebra A A']
    {M : Type w} [AddCommGroup M] [Module A M]
    {M' : Type w'} [AddCommGroup M'] [Module A M'] [Module A' M'] [IsScalarTower A A' M']
    (f : M →ₗ[A] M') (hf : IsBaseChange A' f)
    {n : ℕ} (x : Fin n → M) (φ : Fin n → (M →ₗ[A] A)) (hxφ : ∀ m : M, ∑ i, φ i m • x i = m) :
    ∃ φ' : Fin n → (M' →ₗ[A'] A'),
      (∀ (i : Fin n) (m : M), φ' i (f m) = algebraMap A A' (φ i m)) ∧
        ∀ m' : M', ∑ i, φ' i m' • f (x i) = m' := by sorry
