-- Prove2me | Theorems.Thm_IsLocalRing_isDomain_and_isIntegrallyClosed_adicCompletion_of_formallySmooth_of_ringKrullDim_le_one
-- name    : IsLocalRing.isDomain_and_isIntegrallyClosed_adicCompletion_of_formallySmooth_of_ringKrullDim_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/b25f2bde-fde0-5cce-ac0e-4bf1114361cb
-- title:
--   Completion of a formally smooth local algebra of dimension ≤ 1
-- statement:
--   Let $A_0$ be a discrete valuation ring (a commutative domain with the `IsDiscreteValuationRing` property) and let $q \in A_0$ be an element with $\mathfrak m_{A_0} = (q)$. Let $S$ be a commutative Noetherian local ring equipped with an $A_0$-algebra structure which is essentially of finite type over $A_0$ (i.e. `Algebra.EssFiniteType A₀ S`) and formally smooth over $A_0$, and assume that the image of $q$ under $A_0 \to S$ is a unit of $S$ and that $\operatorname{ringKrullDim} S \le 1$ (an inequality in $\mathbb{N}_\infty$ with a bottom element, so it also forces $S \ne 0$ in the conventions used). Then the $\mathfrak m_S$-adic completion $\widehat S =$ `AdicCompletion (IsLocalRing.maximalIdeal S) S` is a domain, $\widehat S$ is integrally closed in its fraction field, and the image of $q$ in $\widehat S$ (i.e. $q$ pushed through $A_0 \to S \to \widehat S$) is nonzero.
--
--   This is the statement that a Noetherian local algebra of Krull dimension at most one which is essentially of finite type and formally smooth over a discrete valuation ring with the uniformiser inverted has normal (indeed, field or complete discrete valuation) completion: the generic-fibre case of the normality analysis of completed local rings of modular curves. It is used in the treatment of local rings of modular curves at full level in the arguments concerning $\Gamma_0$- and $H$-type level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_isDomain_and_isIntegrallyClosed_adicCompletion_of_formallySmooth_of_ringKrullDim_le_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsLocalRing.isDomain_and_isIntegrallyClosed_adicCompletion_of_formallySmooth_of_ringKrullDim_le_one
    {A₀ : Type} [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] (q : A₀)
    (hA₀q : IsLocalRing.maximalIdeal A₀ = Ideal.span {q})
    (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Algebra A₀ S]
    [Algebra.EssFiniteType A₀ S] [Algebra.FormallySmooth A₀ S]
    (hq : IsUnit (algebraMap A₀ S q)) (hdim : ringKrullDim S ≤ 1) :
    IsDomain (AdicCompletion (IsLocalRing.maximalIdeal S) S) ∧
      IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal S) S) ∧
      algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (algebraMap A₀ S q) ≠ 0 := by sorry
