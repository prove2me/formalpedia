-- Prove2me | Theorems.Thm_OAI_PartialPermutation_normalized_matrixCoefficients_orthonormal
-- name    : OAI.PartialPermutation.normalized_matrixCoefficients_orthonormal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:19:11.246515+00:00
-- url     : https://prove2.me/theorems/6451fa40-9a28-4145-a21e-ef6ac9c18a80
-- title:
--   Schur orthonormality of normalized matrix coefficients
-- statement:
--   Let $G$ be a finite group of order $|G|$ and let $V$ be a finite-dimensional complex inner product space, with inner product $\langle\cdot,\cdot\rangle$ conjugate-linear in the first and linear in the second argument. Let $\rho$ be an irreducible representation of $G$ on $V$ that is unitary, i.e. $\langle\rho(g)x,\rho(g)y\rangle=\langle x,y\rangle$ for all $g\in G$ and $x,y\in V$, and put $d=\dim_{\mathbb{C}}V$. Let $(e_i)_{i\in I}$ be an orthonormal basis of $V$ indexed by a finite set $I$, and equip $\mathbb{C}^G$ with the inner product $\langle a,b\rangle_{\ell^2(G)}=\sum_{g\in G}\overline{a(g)}\,b(g)$. For $(i,j)\in I\times I$ define the normalized (conjugated) matrix coefficient
--   $$
--   v_{ij}(g)=\sqrt{\frac{d}{|G|}}\;\overline{\langle e_i,\rho(g)e_j\rangle}\qquad(g\in G).
--   $$
--   Then the family $(v_{ij})_{(i,j)\in I\times I}$ is orthonormal in $\ell^2(G)$:
--   $$
--   \langle v_{ij},v_{kl}\rangle_{\ell^2(G)}=\frac{d}{|G|}\sum_{g\in G}\langle e_i,\rho(g)e_j\rangle\,\overline{\langle e_k,\rho(g)e_l\rangle}=\delta_{ik}\,\delta_{jl}.
--   $$
--
--   These are the Schur orthogonality relations for the matrix coefficients of a single irreducible unitary representation. Bessel's inequality against this family of $d^2$ orthonormal vectors bounds the Hilbert–Schmidt norm of the Fourier transform at $\rho$ of any function on $G$ by its $\ell^2$ norm.
--
--   **Formalization Note** $\ell^2(G)$ is `EuclideanSpace ℂ G` and the vectors are formed with `WithLp.toLp 2`; the factor is the real square root `Real.sqrt (finrank / card)` cast to a complex number. Unitarity is the hypothesis `IsUnitary ρ`, irreducibility is the instance `Representation.IsIrreducible ρ` (which forces $V\neq0$), and orthonormality is Mathlib's `Orthonormal`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/MatrixCoefficients.lean#L31-L67

import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage

open OAI OAI.PartialPermutation
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
variable {G V : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) [Representation.IsIrreducible ρ]
include hρ

theorem OAI.PartialPermutation.normalized_matrixCoefficients_orthonormal {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℂ V) :
    Orthonormal ℂ (fun p : ι × ι =>
      (Real.sqrt ((Module.finrank ℂ V : ℝ) / Fintype.card G) : ℂ) •
        (WithLp.toLp 2 (fun g : G => conj (inner ℂ (e p.1) (ρ g (e p.2)))))) := by sorry
