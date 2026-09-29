-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_deficitHessian_nonneg
-- name    : HlawkaSchatten.DiagonalConstruction.deficitHessian_nonneg
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T18:19:59.653599+00:00
-- url     : https://prove2.me/theorems/e47f4072-568f-40ed-a0d2-928493721eb4
-- title:
--   Nonnegativity of the Hlawka deficit's Hessian on the cyclic coordinate box
-- statement:
--   Write a *triple* $X$ as three columns $X_0,X_1,X_2\in\mathbb R^3$, with $X_{j,i}$ coordinate $i$ of column $j$ (Lean: `X j i`). Let $\mathrm{pairTriple}(X)_j$ denote the sum of the two columns of $X$ other than $j$ (so $\mathrm{pairTriple}(X)_0=X_1+X_2$, $\mathrm{pairTriple}(X)_1=X_0+X_2$, $\mathrm{pairTriple}(X)_2=X_0+X_1$), and $\mathrm{totalTriple}(X)=X_0+X_1+X_2$. Let $\mathrm{cyclicCenter}$ be the triple whose $j$-th column has $-1$ in position $j$ and $1$ elsewhere, and $\mathrm{entryBox}:=\{X:|X_{j,i}-\mathrm{cyclicCenter}_{j,i}|\le19/100\text{ for all }j,i\}$.
--
--   For $v,h\in\mathbb R^3$, define
--   $$
--   \begin{gathered}
--   \mathrm{normHessian}_p(v,h):=(p-1)\Bigl(\textstyle\sum_i|v_i|^p\Bigr)^{1/p-1}\sum_i|v_i|^{p-2}\bigl(h_i-\mathrm{radialCoefficient}_p(v,h)\,v_i\bigr)^2, \\
--   \quad \mathrm{radialCoefficient}_p(v,h):=\frac{\sum_i|v_i|^{p-2}v_ih_i}{\sum_i|v_i|^p}.
--   \end{gathered}
--   $$
--
--   For $p,K\in\mathbb R$, define the Hessian of the Hlawka deficit at a triple $X$, in direction $Z$ (another triple), as
--   $$
--   \begin{gathered}
--   \mathrm{deficitHessian}_{p,K}(X,Z) := (2K-1)\sum_j \mathrm{normHessian}_p(X_j,Z_j) \\
--   \;+\; \mathrm{normHessian}_p\bigl(\mathrm{totalTriple}(X),\mathrm{totalTriple}(Z)\bigr) \\
--   \;-\; K\sum_j \mathrm{normHessian}_p\bigl(\mathrm{pairTriple}(X)_j,\mathrm{pairTriple}(Z)_j\bigr).
--   \end{gathered}
--   $$
--
--   For every $p\ge256$, every $K$ with $1\le K\le p$, every $X\in\mathrm{entryBox}$, and every triple $Z$,
--   $$0 \;\le\; \mathrm{deficitHessian}_{p,K}(X,Z).$$
--
--   $\mathrm{deficitHessian}$ is built from $\mathrm{normHessian}$ with exactly the combinatorial pattern — three singleton terms with coefficient $2K-1$, one "total" term with coefficient $1$, and three "pair" terms with coefficient $-K$ — that a Hlawka-type deficit $(2K-1)\bigl(N(X_0)+N(X_1)+N(X_2)\bigr)+N(X_0+X_1+X_2)-K\bigl(N(X_0+X_1)+N(X_0+X_2)+N(X_1+X_2)\bigr)$ has in a size functional $N$. Differentiating each of these seven norm-terms twice along the line $X+sZ$ — using that $\mathrm{normHessian}_p$ is exactly the second derivative of the finite coordinate $p$-norm along a line, away from the origin — reproduces $\mathrm{deficitHessian}_{p,K}(X,Z)$ term by term. So this theorem is a statement about curvature: for every admissible $K$ in the stated range, the Hlawka-type deficit built from the finite coordinate $p$-norm has nonnegative second derivative, in every direction $Z$, at every point of the cyclic coordinate box.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/BoxHessian.lean#L40-L88

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxHessian
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Nonnegative second variation on the entire cyclic box -/

open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.deficitHessian_nonneg {p K : ℝ} (hp : 256 ≤ p) (hK : 1 ≤ K) (hKp : K ≤ p)
    {X : Triple} (hX : X ∈ entryBox) (Z : Triple) : 0 ≤ deficitHessian p K X Z := by sorry
