-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_faber_expansion_of_degree
-- name    : OAI.DirectCrouzeix.faber_expansion_of_degree
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:34:21.673972+00:00
-- url     : https://prove2.me/theorems/0a482029-3763-4ded-b821-5a82135e0a8c
-- title:
--   Matrix polynomials expand in any scalar polynomial basis with exact degrees
-- statement:
--   Let $m\ge1$ and let $M_m(\mathbb{C})[z]$ be the ring of polynomials in $z$ with coefficients in $M_m(\mathbb{C})$. Let $b_0,b_1,b_2,\dots\in\mathbb{C}[z]$ be scalar polynomials with
--   $$
--   \deg b_k=k\qquad\text{for every }k\in\mathbb{N}
--   $$
--   (in particular no $b_k$ is the zero polynomial). Then every $G\in M_m(\mathbb{C})[z]$ is a finite combination of the $b_k$ with matrix coefficients: there exist $N\in\mathbb{N}$ and $C_0,\dots,C_{N-1}\in M_m(\mathbb{C})$ such that
--   $$
--   G(z)=\sum_{k=0}^{N-1}C_k\,b_k(z)
--   $$
--   as an identity in $M_m(\mathbb{C})[z]$, where the scalar polynomial $b_k$ is identified with the matrix polynomial $b_k(z)\,I_m$.
--
--   This verifies the expansion hypothesis of the Faber-energy estimates (every matrix polynomial has the form $\sum_kC_kb_k$) for any polynomial sequence of exact degrees, in particular for a sequence of Faber polynomials.
--
--   **Formalization Note** The right-hand side is `faberPolynomial b C`, i.e. the sum over `k : Fin N` of `Polynomial.C (C k) * scalarMatrixPolynomial (b k)`, where `scalarMatrixPolynomial` maps coefficients along $\lambda\mapsto\lambda I_m$. The degree hypothesis is an equality in `WithBot ℕ`. The assumption $m\ge1$ makes $M_m(\mathbb{C})$ a nontrivial ring, so that $b_k(z)I_m$ still has degree $k$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/DomainCore.lean#L119-L151

import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy

open OAI OAI.DirectCrouzeix
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder
open MeasureTheory

theorem OAI.DirectCrouzeix.faber_expansion_of_degree {m : ℕ} (hm : 0 < m)
    (b : ℕ → Polynomial ℂ) (hb : ∀ k, (b k).degree = k) (G : MatrixPolynomial m) :
    ∃ (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ), G = faberPolynomial b C := by sorry
