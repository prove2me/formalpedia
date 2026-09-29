-- Prove2me | Theorems.Thm_HlawkaSchatten_re_trace_comp_eq_sum_eigenbasis_overlap
-- name    : HlawkaSchatten.re_trace_comp_eq_sum_eigenbasis_overlap
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:21:26.281672+00:00
-- url     : https://prove2.me/theorems/6931b5a6-fee4-4b44-8d3d-552a0ec982f9
-- title:
--   Trace of a product of two diagonalizable operators via their eigenbasis overlaps
-- statement:
--   Let $E$ be a finite-dimensional complex inner-product space, and let $A,B:E\to E$ be complex-linear maps with $A$ symmetric (self-adjoint), i.e. $\langle Ax,y\rangle=\langle x,Ay\rangle$ for all $x,y\in E$. Let $(e_i)_{i\in\iota}$ and $(f_j)_{j\in\kappa}$ be orthonormal bases of $E$ indexed by finite sets $\iota,\kappa$, and let $a:\iota\to\mathbb R$, $b:\kappa\to\mathbb R$ be such that $e_i$ is an eigenvector of $A$ with eigenvalue $a_i$ ($A(e_i)=a_ie_i$) and $f_j$ is an eigenvector of $B$ with eigenvalue $b_j$ ($B(f_j)=b_jf_j$), for every $i,j$. Write the *basis overlap* $\operatorname{ov}(e_i,f_j)=|\langle e_i,f_j\rangle|^2$. Then
--
--   $$
--   \operatorname{Re}\operatorname{tr}(A\circ B) = \sum_{(i,j)\in\iota\times\kappa} a_i\, b_j\, \operatorname{ov}(e_i,f_j).
--   $$
--
--   This expands the trace of a product of two diagonalizable operators, each given in its own eigenbasis, into a double sum over pairs of eigenvalues weighted by the squared overlaps of the two eigenbases. It is the key spectral-lift step: applied to the Hermitian dilations of two rectangular operators, it turns trace-level Bregman- and Mazur-type comparison quantities into sums, over pairs of eigenvalues, of the purely scalar Bregman/Mazur comparison — which is where dimension-independent constants can come from.
--
--   **Formalization Note.** Only $A$ is hypothesized symmetric; $B$ is given only through its eigen-relation $B(f_j)=b_jf_j$ with real $b$, not through a separate `IsSymmetric` hypothesis. This is not a genuinely broader class of operators than symmetric ones — an operator that is diagonal with real eigenvalues in some orthonormal basis is automatically self-adjoint — but the proof below never uses any self-adjointness fact about $B$, only the explicit eigen-data $(f,b)$, so stating the hypothesis this way records exactly what the argument needs, not a strictly weaker mathematical assumption. The same observation applies to $A$: the eigen-relation $A(e_i)=a_ie_i$ already forces $A$ to be self-adjoint, so the separately listed hypothesis that $A$ is symmetric is likewise implied by the eigen-data, not an independent restriction.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/HermitianSpectral.lean#L326-L357

import Definitions.Def_HlawkaSchatten_SpectralLift
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Data.Sign.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Finite Hermitian spectral trace expansions

This file connects the overlap-weighted scalar comparison to traces of
finite-dimensional symmetric complex-linear maps.
-/


open scoped InnerProductSpace
open RCLike
open ComplexConjugate

variable {ι κ E : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

open HlawkaSchatten

theorem HlawkaSchatten.re_trace_comp_eq_sum_eigenbasis_overlap [FiniteDimensional ℂ E]
    (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric)
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ E)
    (a : ι → ℝ) (b : κ → ℝ)
    (he : ∀ i, A (e i) = (a i : ℂ) • e i)
    (hf : ∀ j, B (f j) = (b j : ℂ) • f j) :
    ((A.comp B).trace ℂ E).re =
      ∑ ij : ι × κ, a ij.1 * b ij.2 * orthonormalBasisOverlap e f ij := by sorry
