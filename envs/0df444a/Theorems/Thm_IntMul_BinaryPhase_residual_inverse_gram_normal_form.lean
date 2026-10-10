-- Prove2me | Theorems.Thm_IntMul_BinaryPhase_residual_inverse_gram_normal_form
-- name    : IntMul.BinaryPhase.residual_inverse_gram_normal_form
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T17:43:21.800451+00:00
-- url     : https://prove2.me/theorems/92348b18-8f9b-4d7c-9840-f85728f60b46
-- title:
--   One-child normal form for the actual inverse-Gram Hamming-weight residual
-- statement:
--   Let $A$ be a binary matrix whose Gram matrix $G=A^\mathsf{T}A$ is nonsingular, and let its columns be indexed by a finite set $R$. Define the actual residual phase by $q(z)=\operatorname{wt}(AG^{-1}z)\pmod4$. Then
--   $$K(x,y)=2^{-|R|}\sum_{z\in\mathbb F_2^R}i^{q(z)}(-1)^{z^\mathsf{T}(x+y)}$$
--   factors as
--   $$K(x,y)=\varepsilon\,d_L(x)\left(\prod_{j\in R}C(e_L(x)_j,e_R(y)_j)\right)d_R(y),$$
--   for binary linear address isomorphisms $e_L,e_R$, with $\varepsilon^4=1$ and all values of $d_L,d_R$ having fourth power one. Here $C$ has diagonal entry $(1+i)/2$ and off-diagonal entry $(1-i)/2$. This is the matrix-and-Hamming-weight form stated in the construction notes, including nonsingular alternating Gram forms. The proof establishes the polar identity from the matrix formula rather than assuming it. It is an exact transform identity; fixed-tape implementation and its time accounting remain separate.
-- source:
--   CrocSwap/integer-mult-bounds, commit 3b6b66891c0ac888521cf591fe306c6286601d4f, notes/endpoint-gauge-complex.tex, subsection “A normal form for every nondegenerate binary residual”. https://github.com/CrocSwap/integer-mult-bounds/blob/3b6b66891c0ac888521cf591fe306c6286601d4f/notes/endpoint-gauge-complex.tex

import Definitions.Def_IntMul_BinaryQuadraticPhase
import Theorems.Thm_IntMul_BinaryPhase_residual_normal_form
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
open scoped BigOperators Matrix
open IntMul.BinaryPhase

theorem IntMul.BinaryPhase.residual_inverse_gram_normal_form
    {m r : Type*} [Fintype m] [Fintype r] [DecidableEq r] (A : Matrix m r (ZMod 2))
    (hG : IsUnit (Aᵀ * A).det) :
    ∃ (eL eR : (r → ZMod 2) ≃ₗ[ZMod 2] (r → ZMod 2))
      (ε : ℂ) (dL dR : (r → ZMod 2) → ℂ),
      ε ^ 4 = 1 ∧ (∀ x, dL x ^ 4 = 1) ∧ (∀ y, dR y ^ 4 = 1) ∧
      ∀ x y,
        (∑ z : r → ZMod 2,
          (phase (quadraticWeight (A *ᵥ ((Aᵀ * A)⁻¹ *ᵥ z))) : ℂ) *
            sign (z ⬝ᵥ (x + y))) / (2 : ℂ) ^ Fintype.card r =
        ε * dL x * tensorKernel (eL x) (eR y) * dR y := by sorry
