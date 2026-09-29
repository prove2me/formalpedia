-- Prove2me | Theorems.Thm_GaloisRepAdic_detIsCyclotomic_of_isEquiv
-- name    : GaloisRepAdic.detIsCyclotomic_of_isEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/d7c6968d-d035-53cc-99fa-007c2872c718
-- title:
--   Cyclotomic determinant is invariant under equivalence
-- statement:
--   Let $A$ be a commutative local ring and let $\rho_1,\rho_2$ be two-dimensional adic Galois representations over $A$ in the sense of [`GaloisRepAdic`](def/GaloisRep_Adic.html#L16): each consists of a free finite $A$-module $V$ of rank $2$ together with a monoid homomorphism $\rho$ from the group of $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ to $\mathrm{End}_A(V)$ satisfying the adic continuity condition that for every $n$ there is a finite extension $L/\mathbb{Q}$ inside $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ with $\rho(\sigma)v-v \in \mathfrak{m}_A^{\,n}\cdot V$ for all $v\in V$ and all $\sigma$ fixing $L$ pointwise. Assume $\rho_1$ and $\rho_2$ are equivalent, i.e. there exists an $A$-linear isomorphism $\rho_1.V \simeq \rho_2.V$ with $f(\rho_1(\sigma)x)=\rho_2(\sigma)(f(x))$ for all $\sigma$ and $x$. Let $p$ be a natural number and suppose $\rho_1$ has cyclotomic determinant at $p$, meaning that the image of $p$ lies in the maximal ideal of $A$ and that for all $n,a\in\mathbb{N}$ and all $\sigma$ such that $\sigma\mu=\mu^a$ for every $\mu$ with $\mu^{p^n}=1$, one has $\det(\rho_1(\sigma))-a \in (p^n)A$. Then the same two conditions hold for $\rho_2$.
--
--   This records that the condition of having cyclotomic determinant at $p$, in the finite-level form used for the local deformation conditions, depends only on the equivalence class of a two-dimensional adic representation, as is needed for such conditions to cut out subfunctors of the deformation functor. It is used in the corresponding invariance statement for the flat condition, [`GaloisRepAdic.flatCondition_of_isEquiv`](thm.html#GaloisRepAdic.flatCondition_of_isEquiv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_detIsCyclotomic_of_isEquiv.lean

import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRepAdic.detIsCyclotomic_of_isEquiv
    {A : Type} [CommRing A] [IsLocalRing A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {p : ℕ}
    (h : ρ₁.DetIsCyclotomic p) : ρ₂.DetIsCyclotomic p := by sorry
