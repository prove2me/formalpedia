-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_singularValuePowerSum_diagonal
-- name    : HlawkaSchatten.DiagonalConstruction.singularValuePowerSum_diagonal
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T19:03:39.453097+00:00
-- url     : https://prove2.me/theorems/f41bbbd9-94c3-4a1a-8faf-ce14aefcf4e2
-- title:
--   The singular-value power sum of a diagonal operator
-- statement:
--   For a finite index set $\iota$ with decidable equality and $d:\iota\to\mathbb C$, let $\mathrm{diagonalOperator}(d)$ be the $\mathbb C$-linear operator on the complex Euclidean space $\mathbb C^\iota$ whose matrix, in the standard orthonormal basis, is diagonal with entries $d$. For a linear operator $T$ between finite-dimensional complex inner-product spaces and a real exponent $p$, let
--   $$
--   \mathrm{singularValuePowerSum}_p(T) \;:=\; \sum_k \sigma_k(T)^p
--   $$
--   be the sum of the $p$-th powers of the (finitely many nonzero) singular values $\sigma_k(T)$ of $T$.
--
--   For every $p>0$ and every $d:\iota\to\mathbb C$, this theorem shows
--   $$
--   \mathrm{singularValuePowerSum}_p\bigl(\mathrm{diagonalOperator}(d)\bigr) \;=\; \sum_{i\in\iota} |d_i|^p.
--   $$
--
--   This identifies the singular values of a diagonal operator with the moduli of its diagonal entries, at the level of $p$-th power sums. It is the step connecting a coordinate-vector proof of a Hlawka-type bound to the singular-value definition of the Schatten quantity used elsewhere.
--
--   **Formalization Note.** $\mathrm{diagonalOperator}(d)$ denotes the linear map on Mathlib's `EuclideanSpace ℂ ι`, obtained from the diagonal matrix with entries $d$; the hypothesis $p>0$ is only what is needed for the power $\sigma_k(T)^p$ and the exponent $p/2$ used internally in the proof to be well-behaved, not for $\mathrm{singularValuePowerSum}_p$ itself to be a norm-like quantity.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/DiagonalNorm.lean#L60-L74

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

theorem HlawkaSchatten.DiagonalConstruction.singularValuePowerSum_diagonal {p : ℝ} (hp : 0 < p) (d : ι → ℂ) :
    singularValuePowerSum p (diagonalOperator d) = ∑ i, ‖d i‖ ^ p := by sorry
