-- Prove2me | Theorems.Thm_Module_End_finrank_iInf_maxGenEigenspace_baseChange_eq_mul_prod_rootMultiplicity_of_isAlgClosed
-- name    : Module.End.finrank_iInf_maxGenEigenspace_baseChange_eq_mul_prod_rootMultiplicity_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/044ea468-3acd-5ec8-9b17-9c23be8e2a1d
-- title:
--   Joint generalised eigenspace dimensions are independent of the extension field
-- statement:
--   Let $K$ be a field and $W$ a finite-dimensional $K$-vector space, let $Q$ be a finite index set, and for each $q \in Q$ let $U_q$ be a $K$-linear endomorphism of $W$ and $P_q \in K[X]$ a polynomial; let $c$ be a natural number. For a field extension $\Omega$ of $K$ and a tuple $\lambda \in \Omega^Q$, consider the intersection over $q \in Q$ of the maximal generalised eigenspaces of the base-changed endomorphisms $U_q \otimes 1$ on $\Omega \otimes_K W$ for the eigenvalues $\lambda_q$, and compare its $\Omega$-dimension with $c \prod_{q} \operatorname{mult}_{\lambda_q}\bigl(P_q \text{ viewed in } \Omega[X]\bigr)$, the root multiplicities being those of the images of the $P_q$ under the structure map $K[X] \to \Omega[X]$. The hypothesis is that for one algebraically closed extension field $\Omega_1$ of $K$ these two quantities agree for every $\mu \in \Omega_1^Q$. The conclusion is that for every field extension $\Omega_2$ of $K$, not assumed algebraically closed, and every tuple $\mathrm{lam} \in \Omega_2^Q$, the $\Omega_2$-dimension of $\bigcap_q \ker^\infty(U_q \otimes 1 - \mathrm{lam}_q)$ on $\Omega_2 \otimes_K W$ equals $c \prod_q \operatorname{mult}_{\mathrm{lam}_q}(P_q)$ computed in $\Omega_2[X]$.
--
--   This is a descent-and-transfer statement of linear algebra: a dimension formula for joint generalised eigenspaces of a commuting-free family of operators, once verified over a single algebraically closed extension of the base field, holds over every extension field, with both sides read off from polynomials defined over $K$. It is used in the computation of the dimension of the subspace of a cohomology carrier cut out by parabolic conditions together with eigenvalue and generalised-eigenvalue conditions for Hecke operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_End_finrank_iInf_maxGenEigenspace_baseChange_eq_mul_prod_rootMultiplicity_of_isAlgClosed.lean

import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Roots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem Module.End.finrank_iInf_maxGenEigenspace_baseChange_eq_mul_prod_rootMultiplicity_of_isAlgClosed
    {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {Q : Type} [Fintype Q] (U : Q → Module.End K W) (P : Q → Polynomial K) (c : ℕ)
    (Ω₁ : Type) [Field Ω₁] [Algebra K Ω₁] [IsAlgClosed Ω₁]
    (h₁ : ∀ μ : Q → Ω₁, Module.finrank Ω₁
        ↥(⨅ q, Module.End.maxGenEigenspace ((U q).baseChange Ω₁) (μ q)) =
      c * ∏ q, Polynomial.rootMultiplicity (μ q) ((P q).map (algebraMap K Ω₁)))
    (Ω₂ : Type) [Field Ω₂] [Algebra K Ω₂] (lam : Q → Ω₂) :
    Module.finrank Ω₂ ↥(⨅ q, Module.End.maxGenEigenspace ((U q).baseChange Ω₂) (lam q)) =
      c * ∏ q, Polynomial.rootMultiplicity (lam q) ((P q).map (algebraMap K Ω₂)) := by sorry
