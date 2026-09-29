-- Prove2me | Theorems.Thm_IsCyclotomicExtension_Rat_frobenius_comp_algebraMap_eq
-- name    : IsCyclotomicExtension.Rat.frobenius_comp_algebraMap_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/6d74bdc0-801f-50d8-8a28-8776d6ca27fb
-- title:
--   Frobenius fixes the image of a DVR in ℚ(ζₚ) above p
-- statement:
--   Let $p$ be a prime and let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, i.e. $L = \mathbb{Q}(\zeta_p)$. Let $A$ be a discrete valuation domain equipped with an algebra structure over which $L$ is the fraction field of $A$, and assume that $p$, viewed in $A$, lies in the maximal ideal of the local ring $A$; thus $A$ is a valuation ring of $L$ lying above $p$. Let $k$ be a domain of characteristic $p$ together with an $A$-algebra structure. The conclusion is an equality of ring homomorphisms $A \to k$: the structure map $\operatorname{algebraMap} A k$ followed by the Frobenius endomorphism $x \mapsto x^p$ of $k$ equals $\operatorname{algebraMap} A k$ itself. Equivalently, $\varphi(a)^p = \varphi(a)$ for every $a \in A$, where $\varphi$ is the structure map; that is, the image of $A$ in $k$ consists of elements fixed by Frobenius.
--
--   This records the arithmetic content that $p$ is totally ramified in $\mathbb{Q}(\zeta_p)$, so that the residue field of such an $A$ is the prime field $\mathbb{F}_p$ and every $A$-algebra which is a domain of characteristic $p$ receives only Frobenius-fixed elements from $A$. It is used in the analysis of the reduction of the modular curve $X_1(p)$ and of Hecke correspondences in characteristic $p$, where it makes the Frobenius of $\operatorname{Spec} k$ a morphism over $\operatorname{Spec} A$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsCyclotomicExtension_Rat_frobenius_comp_algebraMap_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsCyclotomicExtension.Rat.frobenius_comp_algebraMap_eq
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    (k : Type*) [CommRing k] [IsDomain k] [CharP k p] [Algebra A k] :
    (frobenius k p).comp (algebraMap A k) = algebraMap A k := by sorry
