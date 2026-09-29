-- Prove2me | Theorems.Thm_IsIntegrallyClosed_ringKrullDim_localization_tensor_eq_one_of_irreducible
-- name    : IsIntegrallyClosed.ringKrullDim_localization_tensor_eq_one_of_irreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/cd602925-9d0a-536a-9ebc-3c69cc69beb1
-- title:
--   Fibre k⊗_Λ A has Krull dimension one at each maximal ideal
-- statement:
--   Let $\Lambda$ be a commutative principal ideal domain and let $p\in\Lambda$ be irreducible. Let $A$ be a Noetherian integrally closed commutative domain carrying both a $\Lambda$-algebra structure and a $\Lambda[X]$-algebra structure which are compatible (the scalar tower condition for $\Lambda\to\Lambda[X]\to A$), such that $A$ is a finite $\Lambda[X]$-module and the $\Lambda[X]$-action on $A$ is faithful, i.e. the structure map $\Lambda[X]\to A$ is injective. Let $k$ be a field, in an arbitrary universe, equipped with a $\Lambda$-algebra structure for which the image of $p$ in $k$ is zero. Then for every maximal ideal $\mathfrak m$ of the tensor product $k\otimes_\Lambda A$, the localisation of $k\otimes_\Lambda A$ at $\mathfrak m$ has Krull dimension exactly $1$ (equality of `ringKrullDim`, valued in the extended integers, with $1$). No irreducibility, reducedness or flatness of the fibre is assumed or asserted; the assertion is purely about the local dimension at each maximal ideal.
--
--   This is the statement that the geometric special fibre at $p$ of a finite, faithful, normal $\Lambda[X]$-algebra is equidimensional of dimension one, i.e. a curve over $k$. It is the version for an abstract $\Lambda[X]$-algebra structure; the companion result [`Subalgebra.ringKrullDim_localization_tensor_eq_one_of_irreducible`](thm.html#Subalgebra.ringKrullDim_localization_tensor_eq_one_of_irreducible) deduces from it the corresponding statement for subalgebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsIntegrallyClosed_ringKrullDim_localization_tensor_eq_one_of_irreducible.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct Polynomial

universe u v

theorem IsIntegrallyClosed.ringKrullDim_localization_tensor_eq_one_of_irreducible
    {Λ A : Type u} [CommRing Λ] [IsDomain Λ] [IsPrincipalIdealRing Λ] {p : Λ} (hp : Irreducible p)
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra Λ A] [Algebra Λ[X] A] [IsScalarTower Λ Λ[X] A]
    [Module.Finite Λ[X] A] [FaithfulSMul Λ[X] A]
    (k : Type v) [Field k] [Algebra Λ k] (hk : algebraMap Λ k p = 0)
    (m : Ideal (k ⊗[Λ] A)) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = 1 := by sorry
