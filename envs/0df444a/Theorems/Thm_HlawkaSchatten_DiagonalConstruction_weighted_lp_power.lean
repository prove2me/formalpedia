-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_weighted_lp_power
-- name    : HlawkaSchatten.DiagonalConstruction.weighted_lp_power
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T17:47:40.681813+00:00
-- url     : https://prove2.me/theorems/eef63858-9c34-4708-9172-4c6e6aa1983a
-- title:
--   A weighted power estimate for coordinate $p$-norms of a real triple
-- statement:
--   Let $\iota$ be a finite index set, $p>1$ a real exponent, and $x,y,z:\iota\to\mathbb{R}$. Write $\mathrm{lpNorm}_p(v) = \big(\sum_{i\in\iota}|v_i|^p\big)^{1/p}$ for the coordinate $p$-norm. The theorem states
--
--   $$
--   \begin{gathered}
--   \frac{\mathrm{lpNorm}_p(x+y)^{p}}{\big(\mathrm{lpNorm}_p(x)+\mathrm{lpNorm}_p(y)\big)^{p-1}} \\
--   + \frac{\mathrm{lpNorm}_p(x+z)^{p}}{\big(\mathrm{lpNorm}_p(x)+\mathrm{lpNorm}_p(z)\big)^{p-1}} \\
--   + \frac{\mathrm{lpNorm}_p(y+z)^{p}}{\big(\mathrm{lpNorm}_p(y)+\mathrm{lpNorm}_p(z)\big)^{p-1}}
--   \end{gathered}
--   $$
--   $$
--   \begin{gathered}
--   \le\;
--   \mathrm{lpNorm}_p(x)+\mathrm{lpNorm}_p(y)+\mathrm{lpNorm}_p(z) \\
--   + \frac{\mathrm{lpNorm}_p(x+y+z)^{p}}{\big(\mathrm{lpNorm}_p(x)+\mathrm{lpNorm}_p(y)+\mathrm{lpNorm}_p(z)\big)^{p-1}}.
--   \end{gathered}
--   $$
--
--   This is a dimension-independent power-sum estimate for the coordinate $p$-norm of a real triple. It underlies both a coarse, fully explicit Hlawka-type constant for the coordinate $p$-norm and a total-norm-dependent envelope for the sum of pairwise norms, each used to confine a hypothetical counterexample to the sharp diagonal Hlawka inequality.
--
--   **Formalization Note** No hypothesis excludes $x$, $y$, or $z$ from being zero. Lean's division convention returns $0$ when the denominator is $0$; whenever a denominator such as $\mathrm{lpNorm}_p(x)+\mathrm{lpNorm}_p(y)$ vanishes, both $x$ and $y$ are $0$ (by positive-definiteness of $\mathrm{lpNorm}_p$) and the matching numerator vanishes with it, so the displayed inequality remains meaningful for every triple.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/ScalarBounds.lean#L78-L101

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
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

open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.weighted_lp_power {p : ℝ} (hp : 1 < p) (x y z : ι → ℝ) :
    lpNorm p (x + y) ^ p / (lpNorm p x + lpNorm p y) ^ (p - 1) +
      lpNorm p (x + z) ^ p / (lpNorm p x + lpNorm p z) ^ (p - 1) +
      lpNorm p (y + z) ^ p / (lpNorm p y + lpNorm p z) ^ (p - 1) ≤
    lpNorm p x + lpNorm p y + lpNorm p z +
      lpNorm p (x + y + z) ^ p / (lpNorm p x + lpNorm p y + lpNorm p z) ^ (p - 1) := by sorry
