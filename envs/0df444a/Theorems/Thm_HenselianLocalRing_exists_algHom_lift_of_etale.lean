-- Prove2me | Theorems.Thm_HenselianLocalRing_exists_algHom_lift_of_etale
-- name    : HenselianLocalRing.exists_algHom_lift_of_etale
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/9a5fb0c9-625f-5e62-af68-2399f9c05758
-- title:
--   Residue-field points of étale algebras lift over Henselian local rings
-- statement:
--   Let $R$ be a commutative ring in a universe $u$ which is a Henselian local ring in Mathlib's sense, and write $\kappa =$ `IsLocalRing.ResidueField R` for its residue field. Let $S$ be a commutative ring in the same universe $u$, equipped with an $R$-algebra structure which is étale (`Algebra.Etale R S`, i.e. formally étale and of finite presentation over $R$). Let $\varphi : S \to \kappa$ be a homomorphism of $R$-algebras. The assertion is that there exists an $R$-algebra homomorphism $\psi : S \to R$ such that for every $s \in S$ the image of $\psi(s)$ under the structure map $R \to \kappa$ equals $\varphi(s)$; that is, $\psi$ lifts $\varphi$ through the residue map, $\psi(s) \bmod \mathfrak{m}_R = \varphi(s)$ for all $s$. Geometrically, every $\kappa$-point of $\operatorname{Spec} S$ over the closed point of $\operatorname{Spec} R$ is the specialisation of a section of $\operatorname{Spec} S \to \operatorname{Spec} R$. Note that $R$ and $S$ are required to lie in a common universe.
--
--   This is the standard lifting criterion characterising Henselian local rings in terms of étale algebras (condition (8) in the usual list of equivalent formulations). It is used in this development to produce sections of étale morphisms over Henselian local rings, both in the algebraic form for complete local rings and in the scheme-theoretic form asserting that an étale morphism admits a section through a prescribed point over the closed point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HenselianLocalRing_exists_algHom_lift_of_etale.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem HenselianLocalRing.exists_algHom_lift_of_etale
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (φ : S →ₐ[R] IsLocalRing.ResidueField R) :
    ∃ ψ : S →ₐ[R] R, ∀ s : S, algebraMap R (IsLocalRing.ResidueField R) (ψ s) = φ s := by sorry
