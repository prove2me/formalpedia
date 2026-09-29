-- Prove2me | Theorems.Thm_GaloisRepAdic_isOrdinaryAt_baseChangeAlong
-- name    : GaloisRepAdic.isOrdinaryAt_baseChangeAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/2518cbf7-51de-57b7-942b-c64fddf18b5e
-- title:
--   Ordinarity at p is preserved by base change along a local homomorphism
-- statement:
--   Let $A$ and $B$ be commutative local rings and let $\varphi\colon A\to B$ be a ring homomorphism which is local (it carries non-units to non-units). Let $\rho$ be a [`GaloisRepAdic`](def/GaloisRep_Adic.html#L16) over $A$: a free finite $A$-module $V$ with $\mathrm{rank}_A V = 2$ together with a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, realised as the $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`, to $\mathrm{End}_A V$, subject to the adic continuity condition that for every $n$ there is a finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ such that every $\sigma$ fixing $L$ pointwise satisfies $\rho(\sigma)v - v \in \mathfrak m_A^n\cdot V$ for all $v\in V$. Assume $\rho$ is ordinary at a natural number $p$, that is: for every valuation subring $P$ of $\overline{\mathbb Q}$ with $p$ a non-unit of $P$, there is an $A$-submodule $L\subseteq V$ of the form $A\cdot b_0$ for some $A$-basis $(b_0,b_1)$ of $V$, such that $L$ is stable under $\rho(\sigma)$ for all $\sigma$ in the decomposition subgroup of $P$ over $\mathbb Q$, and $\rho(\sigma)v - v \in L$ for all $v\in V$ and all $\sigma$ in the image in the decomposition subgroup of the inertia subgroup of $P$ over $\mathbb Q$. Then the base change of $\rho$ along $\varphi$, namely $B\otimes_A V$ with $\sigma$ acting by $\rho(\sigma)\otimes_A \mathrm{id}$ extended $B$-linearly, is again ordinary at $p$. No primality of $p$ is assumed.
--
--   This is one of the compatibilities showing that the ordinary local condition behaves as a deformation condition in Mazur's sense, so that it cuts out a subfunctor stable under extension of the coefficient ring. It is invoked wherever ordinary deformation data are transported along a local homomorphism of coefficient rings, for instance when an ordinary representation is pushed forward to a quotient or to a Hecke algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isOrdinaryAt_baseChangeAlong.lean

import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRepAdic.isOrdinaryAt_baseChangeAlong
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    {p : ℕ} (h : ρ.IsOrdinaryAt p) : (ρ.baseChangeAlong φ hφ).IsOrdinaryAt p := by sorry
