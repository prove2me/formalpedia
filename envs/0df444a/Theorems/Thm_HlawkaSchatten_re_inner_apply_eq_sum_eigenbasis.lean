-- Prove2me | Theorems.Thm_HlawkaSchatten_re_inner_apply_eq_sum_eigenbasis
-- name    : HlawkaSchatten.re_inner_apply_eq_sum_eigenbasis
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:21:06.268559+00:00
-- url     : https://prove2.me/theorems/8b82948b-6dbc-48ab-bf7b-8540d2c71f2e
-- title:
--   Spectral expansion of a symmetric operator's quadratic form against its eigenbasis
-- statement:
--   Let $E$ be a complex inner-product space and let $A:E\to E$ be a symmetric (self-adjoint) complex-linear map, meaning $\langle Ax,y\rangle=\langle x,Ay\rangle$ for all $x,y\in E$. Let $\iota$ be a finite index set, let $(e_i)_{i\in\iota}$ be an orthonormal basis of $E$, and let $a:\iota\to\mathbb R$ be such that each $e_i$ is an eigenvector of $A$ with eigenvalue $a_i$, i.e. $A(e_i)=a_i\,e_i$ for every $i$. Then, for every $x\in E$,
--
--   $$
--   \operatorname{Re}\langle x, Ax\rangle = \sum_{i\in\iota} a_i\, |\langle e_i, x\rangle|^2 .
--   $$
--
--   This is the spectral expansion of the (real) quadratic form of a symmetric operator against its eigenbasis: writing $x$ in eigen-coordinates, $\langle x,Ax\rangle$ decomposes into a weighted sum of the eigenvalues $a_i$, weighted by the squared eigen-coordinates $|\langle e_i,x\rangle|^2$. It is the first step of the spectral-lift layer: applied to the Hermitian dilations of a pair of rectangular operators, it lets Bregman-type and Mazur-type trace quantities be rewritten as sums over eigenvalues weighted by basis overlaps.
--
--   **Formalization Note.** Having an orthonormal basis indexed by a finite set $\iota$ makes $E$ finite-dimensional as a consequence, not as a separately stated hypothesis; the theorem places no other restriction on $E$, $A$, or $x$.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/HermitianSpectral.lean#L298-L324

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

theorem HlawkaSchatten.re_inner_apply_eq_sum_eigenbasis
    (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric)
    (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ)
    (he : ∀ i, A (e i) = (a i : ℂ) • e i) (x : E) :
    (⟪x, A x⟫_ℂ).re = ∑ i, a i * ‖(⟪e i, x⟫_ℂ)‖ ^ 2 := by sorry
