-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_lp_hlawka_le_exponent
-- name    : HlawkaSchatten.DiagonalConstruction.lp_hlawka_le_exponent
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T17:50:58.982665+00:00
-- url     : https://prove2.me/theorems/a5f90c49-c24e-4d09-9623-fe0361c917cd
-- title:
--   A rough, dimension-independent Hlawka constant of size $p$ for coordinate $p$-norms
-- statement:
--   Let $\iota$ be a finite index set, $p>1$ a real exponent, and $x,y,z:\iota\to\mathbb{R}$. Write
--
--   $$
--   \mathrm{lpNorm}_p(v) = \Big(\sum_{i\in\iota}|v_i|^p\Big)^{1/p}
--   $$
--
--   for the coordinate $p$-norm of $v:\iota\to\mathbb{R}$. For a size functional $N$ and vectors $u,v$, call $N(u)+N(v)-N(u+v)$ their *pair deficit*. For the triple $x,y,z$, define the *triple deficit*
--
--   $$
--   \mathrm{tripleGap}(x,y,z) = \mathrm{lpNorm}_p(x)+\mathrm{lpNorm}_p(y)+\mathrm{lpNorm}_p(z) - \mathrm{lpNorm}_p(x+y+z),
--   $$
--
--   and the *pair-deficit sum* $\mathrm{pairGapSum}(x,y,z)$, the sum of the three pair deficits of $\mathrm{lpNorm}_p$ taken over $\{x,y\}$, $\{x,z\}$, and $\{y,z\}$. The theorem states
--
--   $$
--   \mathrm{tripleGap}(x,y,z) \;\le\; p\cdot \mathrm{pairGapSum}(x,y,z).
--   $$
--
--   Equivalently, the exponent $p$ itself is an admissible Hlawka constant for the coordinate $p$-norm on $\iota\to\mathbb{R}$, for every finite index set $\iota$.
--
--   This is a rough but fully explicit Hlawka constant: it is dimension-independent, exponent-explicit, and needs no localization or curvature analysis. It also controls triples whose pair-deficit sum vanishes, forcing their triple deficit to be exactly zero as well (the triangle inequality already gives $\mathrm{tripleGap}(x,y,z)\ge0$ whenever $p\ge1$).
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/ScalarBounds.lean#L137-L158

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# The weighted scalar estimate for arbitrary coordinate triples

The weights are the three input norms. Applying the scalar convexity
inequality coordinate by coordinate yields the dimension-independent power
estimate used to confine a hypothetical counterexample.
-/








variable {ι : Type*} [Fintype ι]

open HlawkaSchatten
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.lp_hlawka_le_exponent {p : ℝ} (hp : 1 < p) (x y z : ι → ℝ) :
    tripleGap (lpNorm p) x y z ≤ p * pairGapSum (lpNorm p) x y z := by sorry
