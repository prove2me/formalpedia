-- Prove2me | Theorems.Thm_IsLocalRing_exists_monic_aeval_eq_zero_map_residue_eq_pow_iff_residue_eq_of_injective
-- name    : IsLocalRing.exists_monic_aeval_eq_zero_map_residue_eq_pow_iff_residue_eq_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/1b459450-bee0-55fb-9f66-5daa1e9d336c
-- title:
--   Residual characterisation of x modulo mathfrak m_A by monic polynomials
-- statement:
--   Let $\mathcal O$ be a commutative local ring and let $A$ be a commutative local ring equipped with an $\mathcal O$-algebra structure which is finite and free as an $\mathcal O$-module and whose structure map $\mathcal O \to A$ is a local homomorphism (it carries the maximal ideal into the maximal ideal). Let $F$ be a further commutative $\mathcal O$-algebra, let $j \colon A \to F$ be an injective homomorphism of $\mathcal O$-algebras, let $x \in A$, and let $c$ be an element of the residue field $\mathcal O/\mathfrak m_{\mathcal O}$. The assertion is an equivalence. The left-hand side says that there exists a monic polynomial $R \in \mathcal O[X]$ with $R(j(x)) = 0$ in $F$ and whose reduction modulo $\mathfrak m_{\mathcal O}$ equals $(X - c)^{\deg R}$ in $(\mathcal O/\mathfrak m_{\mathcal O})[X]$, where $\deg R$ is the natural-number degree of $R$. The right-hand side says that the image of $x$ in the residue field of $A$ equals the image of $c$ under the induced map $\mathcal O/\mathfrak m_{\mathcal O} \to A/\mathfrak m_A$.
--
--   The left-hand condition is a polynomial substitute for the congruence $x \equiv c$ that makes sense in an $\mathcal O$-algebra carrying no residue map of its own, for instance an algebraic closure of the fraction field of $\mathcal O$; the theorem says that for an element of a finite free local $\mathcal O$-algebra embedded in such an algebra the condition is exactly the congruence modulo the maximal ideal of $A$. It is used in the construction of newforms with prescribed residual behaviour, where eigenvalues (unit roots, values $\pm 1$ of $a_q$) are handed over as elements of an algebraic closure and must be converted into residual information.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_monic_aeval_eq_zero_map_residue_eq_pow_iff_residue_eq_of_injective.lean

import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Polynomial.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial IsLocalRing

theorem IsLocalRing.exists_monic_aeval_eq_zero_map_residue_eq_pow_iff_residue_eq_of_injective
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A] [Module.Free 𝒪 A]
    [IsLocalHom (algebraMap 𝒪 A)]
    {F : Type} [CommRing F] [Algebra 𝒪 F]
    (j : A →ₐ[𝒪] F) (hj : Function.Injective j) (x : A) (c : IsLocalRing.ResidueField 𝒪) :
    (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (j x) R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C c) ^ R.natDegree) ↔
      IsLocalRing.residue A x = IsLocalRing.ResidueField.map (algebraMap 𝒪 A) c := by sorry
