-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_complex_hlawka_bound
-- name    : HlawkaSchatten.DiagonalConstruction.complex_hlawka_bound
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T18:56:31.835118+00:00
-- url     : https://prove2.me/theorems/ffaf5c43-759c-4f20-a460-25ac82396564
-- title:
--   The Hlawka inequality for complex coordinate $p$-norms with constant $K_p$, for $p\ge256$
-- statement:
--   For a finite index set $\iota$ of any size (including the empty set, i.e. dimension zero) and a real exponent $p$, write
--   $$
--   \|v\|_p := \Big(\sum_{i\in\iota}|v_i|^p\Big)^{1/p}
--   $$
--   for the finite coordinate $p$-norm of a complex vector $v:\iota\to\mathbb C$ (with $|\cdot|$ the complex modulus; a norm for $p\ge1$). For $x,y,z:\iota\to\mathbb C$ put
--   $$
--   S=\|x\|_p+\|y\|_p+\|z\|_p,\qquad T=\|x+y+z\|_p,\qquad P=\|x+y\|_p+\|x+z\|_p+\|y+z\|_p.
--   $$
--
--   Let $K_p$ be the following explicit constant: with
--   $$
--   A_p(t)=(t^p+2)^{1/p},\qquad B_p(t)=(2|1-t|^p+2^p)^{1/p},\qquad R_p(t)=\frac{3A_p(t)-3^{1/p}|2-t|}{6A_p(t)-3B_p(t)},
--   $$
--   $$
--   K_p := \sup\{R_p(t) : \tfrac12\le t\le2\}.
--   $$
--   ($A_p(t)$ and $B_p(t)$ are the coordinate $p$-norms of the cyclic triple $(-t,1,1),(1,-t,1),(1,1,-t)$ and of its pairwise sums, and $R_p$ is the corresponding value of $(S-T)/(2S-P)$ for that triple.)
--
--   This theorem shows that for every real $p\ge256$, every finite index set $\iota$, and every $x,y,z:\iota\to\mathbb C$,
--   $$
--   S - T \;\le\; K_p\,(2S-P).
--   $$
--
--   This theorem gives the existence half of the sharp diagonal Hlawka inequality for complex coordinate norms: for every $p\ge256$, the explicit constant $K_p$ is admissible, dimension-independently, with no assumption that $x,y,z$ have equal norms. A companion theorem shows that any constant admissible for the complex coordinate $p$-norm on $\mathbb C^n$ in some fixed dimension $n\ge3$ is at least $K_p$, for every $p>1$; combined with that lower bound, this theorem is what makes $K_p$ the sharp (smallest possible) Hlawka constant for the coordinate $p$-norm on $\mathbb C^n$ in every dimension $n\ge3$ — equivalently, the smallest constant valid in all those finite dimensions at once — for every $p\ge256$. On its own, this theorem concerns the coordinate $\ell^p$-quantity $\|\cdot\|_p$ on $\mathbb C^\iota$; a companion identity, showing that this same quantity equals the Schatten $p$-norm of the diagonal operator with entries $v$, carries the bound over to complex diagonal Schatten $p$-norms.
--
--   **Formalization Note** The index set $\iota$ ranges over an arbitrary finite type (via a `Fintype` instance), not just `Fin n`, and may be empty.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/ComplexTransfer.lean#L82-L120

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Transfer to complex coordinates

Finite convex combinations of real circle projections obey the real bound.
Continuity preserves this statement on their closure. The circle average
belongs to that closure and reproduces all seven complex norms with one
common positive factor.
-/


open MeasureTheory





variable {ι : Type*} [Fintype ι]

open HlawkaSchatten
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.complex_hlawka_bound {p : ℝ} (hp : 256 ≤ p) :
    HasHlawkaConstant (lpNorm p : (ι → ℂ) → ℝ) (cyclicConstant p) := by sorry
