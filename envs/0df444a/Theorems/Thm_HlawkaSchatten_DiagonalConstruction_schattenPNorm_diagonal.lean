-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_schattenPNorm_diagonal
-- name    : HlawkaSchatten.DiagonalConstruction.schattenPNorm_diagonal
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T19:05:53.920607+00:00
-- url     : https://prove2.me/theorems/766afe31-f3fa-4572-87c0-dfaa919e9a36
-- title:
--   The Schatten $p$-norm of a diagonal operator equals the coordinate $\ell^p$-norm
-- statement:
--   For a finite index set $\iota$ with decidable equality and $d:\iota\to\mathbb C$, let $\mathrm{diagonalOperator}(d)$ be the $\mathbb C$-linear operator on the complex Euclidean space $\mathbb C^\iota$ obtained from the diagonal matrix with entries $d$ (diagonal in the standard orthonormal basis). For a linear operator $T$ between finite-dimensional complex inner-product spaces, write $\sigma_k(T)$ for its singular values and, for a real exponent $p$,
--   $$
--   \mathrm{schattenPNorm}_p(T) \;:=\; \Bigl(\sum_k \sigma_k(T)^p\Bigr)^{1/p}
--   $$
--   for the $1/p$-th power of the sum of $p$-th powers of the (finitely many nonzero) singular values of $T$; and for $v:\iota\to\mathbb C$ let $\|v\|_p:=\bigl(\sum_i|v_i|^p\bigr)^{1/p}$ be the finite coordinate $p$-norm.
--
--   For every $p>0$ and every $d:\iota\to\mathbb C$, this theorem shows
--   $$
--   \mathrm{schattenPNorm}_p\bigl(\mathrm{diagonalOperator}(d)\bigr) \;=\; \|d\|_p.
--   $$
--
--   This identifies the Schatten $p$-quantity of a complex diagonal operator exactly with the coordinate $\ell^p$-norm of its diagonal entries, for every positive exponent $p$. Combined with a coordinate-vector Hlawka bound proved separately for $\|\cdot\|_p$ on $\mathbb C^\iota$, this identity transports that bound verbatim to $\mathrm{schattenPNorm}_p$ of diagonal operators.
--
--   **Formalization Note.** $\mathrm{diagonalOperator}(d)$ denotes the linear map on the Hilbert-space model $\mathbb C^\iota$ (Mathlib's `EuclideanSpace`) obtained from the diagonal matrix with entries $d$ via the standard matrix-to-linear-map coercion, not an abstract matrix; $\mathrm{schattenPNorm}$ is evaluated on this operator. The hypothesis is only $p>0$: the Schatten quantity is defined, and this identity holds, for every positive exponent, and it is a norm, with the triangle inequality, for $p\ge1$.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/DiagonalNorm.lean#L76-L80

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_DiagonalNorm
import Definitions.Def_HlawkaSchatten_SchattenNorm
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Diagonal operators and coordinate power sums

This connects the coordinate proof to the singular-value Schatten norm
used in the publication boundary. The Gram operator has the coordinate
basis as an eigenbasis, with eigenvalues equal to squared entry norms.
-/


open scoped InnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open HlawkaSchatten
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.schattenPNorm_diagonal {p : ℝ} (hp : 0 < p) (d : ι → ℂ) :
    schattenPNorm p (diagonalOperator d) = lpNorm p d := by sorry
