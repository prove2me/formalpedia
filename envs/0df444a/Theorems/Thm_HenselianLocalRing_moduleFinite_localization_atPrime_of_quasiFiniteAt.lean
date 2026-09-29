-- Prove2me | Theorems.Thm_HenselianLocalRing_moduleFinite_localization_atPrime_of_quasiFiniteAt
-- name    : HenselianLocalRing.moduleFinite_localization_atPrime_of_quasiFiniteAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/9eac90b1-f7bc-54db-8733-255dccb0d418
-- title:
--   Module-finiteness of S_q over a henselian local ring
-- statement:
--   Let $R$ be a commutative ring which is a henselian local ring, with maximal ideal $\mathfrak m_R$, and let $S$ be a commutative $R$-algebra of finite type. Let $\mathfrak q$ be a prime ideal of $S$ whose contraction along the structure map $R \to S$ is exactly $\mathfrak m_R$, so that $\mathfrak q$ lies over the closed point of $\operatorname{Spec} R$, and assume in addition the hypothesis `Algebra.QuasiFiniteAt R q`, expressing that $S$ is quasi-finite over $R$ at $\mathfrak q$. The conclusion is that the localisation $S_{\mathfrak q}$, formed as `Localization.AtPrime q`, is a finite $R$-module, i.e. finitely generated as a module over $R$ for the $R$-algebra structure obtained from that of $S$. No separatedness, flatness or noetherian hypothesis on $R$ or $S$ is imposed beyond those stated.
--
--   This is the pointwise form of the structure theory of quasi-finite algebras over a henselian local ring: a point of $\operatorname{Spec} S$ that is quasi-finite over the closed point of $\operatorname{Spec} R$ has a local ring which is already module-finite over $R$ (EGA IV 18.5.11). It is used further on in the construction of module-finite quotients of finite-type algebras over henselian, in particular discretely valued, base rings, and in the factorisation statement for elements of a valuation subring outside the image of the maximal ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HenselianLocalRing_moduleFinite_localization_atPrime_of_quasiFiniteAt.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

universe u v

theorem HenselianLocalRing.moduleFinite_localization_atPrime_of_quasiFiniteAt
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (q : Ideal S) [q.IsPrime] (hq : q.comap (algebraMap R S) = maximalIdeal R) [Algebra.QuasiFiniteAt R q] :
    Module.Finite R (Localization.AtPrime q) := by sorry
