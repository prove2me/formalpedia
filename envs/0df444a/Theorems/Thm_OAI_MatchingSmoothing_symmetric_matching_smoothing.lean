-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_symmetric_matching_smoothing
-- name    : OAI.MatchingSmoothing.symmetric_matching_smoothing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:45:17.335039+00:00
-- url     : https://prove2.me/theorems/dd2f1b73-e53c-4dd6-87ad-1ebbe4cf80af
-- title:
--   Relabelling-invariant symmetric kernels act with small norm on high-degree functions of perfect matchings
-- statement:
--   Fix $h\in\mathbb N$ and the vertex set $V_h=\{0,\dots,h-1\}\times\{0,1\}$, which has $2h$ elements. Let $\mathcal M_h$ be the finite set of perfect matchings of $V_h$, encoded as fixed-point-free involutions $M$ of $V_h$, and give $\mathbb R^{\mathcal M_h}$ the inner product $\langle f,g\rangle=\sum_{M}f(M)g(M)$ with norm $\|f\|$. For an ordered pair $(u,v)$ of vertices let $x_{(u,v)}(M)=1$ if $M(u)=v$ and $0$ otherwise, and let $\mathcal P_d\subseteq\mathbb R^{\mathcal M_h}$ be the span of all products of at most $d$ such edge indicators (including the constant $1$). A permutation $p$ of $V_h$ relabels a matching $M$ as $pMp^{-1}$.
--
--   Let $k\in\mathbb N$ with $4k<h$. Let $A=(A_{M,N})_{M,N\in\mathcal M_h}$ be a real symmetric matrix that is invariant under simultaneous relabelling,
--
--   $$
--   A_{pMp^{-1},\,pNp^{-1}}=A_{M,N}\qquad\text{for all permutations }p\text{ of }V_h\text{ and all }M,N\in\mathcal M_h,
--   $$
--
--   and let $H,a\in\mathbb R$ with $a\ge0$ and $\operatorname{tr}(A^2)\le H\le\binom hk a^2$. Then every $f\in\mathbb R^{\mathcal M_h}$ orthogonal to $\mathcal P_{16k^2}$ satisfies
--
--   $$
--   \langle f,Af\rangle=\sum_{M,N\in\mathcal M_h}f(M)\,A_{M,N}\,f(N)\;\le\;a\,\|f\|^2 .
--   $$
--
--   A trace bound alone only controls the eigenvalues of $A$ by $\sqrt H$. On functions with no component of degree at most $16k^2$ the theorem gains the factor $\binom hk^{-1/2}$, reflecting the fact that, by symmetry, every nonzero eigenvalue of $A$ compressed to this high-degree part has multiplicity at least $\binom hk$. Applied to relabelling-invariant incidence kernels built from colorings, it shows that averaging over color-table classes nearly annihilates high-degree functions of perfect matchings.
--
--   **Formalization Note** The matrix acts on `EuclideanSpace ℝ (Pairing (Vertices h))` through `Matrix.toEuclideanLin`, and for a real matrix `A.IsHermitian` means symmetry. The degree is written `(4*k)*(4*k)`, and $\mathcal P_d$ is `polynomialSpace h d`, the preimage of `lowDegree Pairing.edgeCoord d` under the identification of the Euclidean space with functions on pairings.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/PolynomialSpaces.lean#L93-L118

import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces

open OAI OAI.MatchingSmoothing
open scoped RealInnerProductSpace

theorem OAI.MatchingSmoothing.symmetric_matching_smoothing {h : ℕ} (k : ℕ) (hk : 4*k < h)
    (A : Matrix (Pairing (Vertices h)) (Pairing (Vertices h)) ℝ)
    (hA : A.IsHermitian)
    (heq : ∀ p M N, A (Pairing.relabel p M) (Pairing.relabel p N) = A M N)
    (H a : ℝ) (ha : 0 ≤ a)
    (htrace : Matrix.trace (A * A) ≤ H)
    (hHa : H ≤ (h.choose k : ℝ) * a ^ 2)
    (f : MatchingSpace h) (hf : f ∈ (polynomialSpace h ((4*k)*(4*k)))ᗮ) :
    ⟪f, A.toEuclideanLin f⟫ ≤ a * ‖f‖ ^ 2 := by sorry
