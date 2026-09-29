-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_normalized_pair_sum_le
-- name    : HlawkaSchatten.DiagonalConstruction.normalized_pair_sum_le
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T18:36:34.480305+00:00
-- url     : https://prove2.me/theorems/6ca4e966-df4b-4ce9-ace8-7a80ec6ba4dc
-- title:
--   The total-norm envelope for a normalized coordinate triple
-- statement:
--   Let $\iota$ be a finite index set, $p>1$, and $x,y,z:\iota\to\mathbb{R}$ nonzero vectors whose coordinate $p$-norms sum to one,
--
--   $$
--   \mathrm{lpNorm}_p(x)+\mathrm{lpNorm}_p(y)+\mathrm{lpNorm}_p(z)=1.
--   $$
--
--   Define the scalar envelope root
--
--   $$
--   \rho_p(q) = \Big(\frac{1+q^p}{2}\Big)^{1/p}, \qquad q\ge0.
--   $$
--
--   The theorem states
--
--   $$
--   \mathrm{lpNorm}_p(x+y) + \mathrm{lpNorm}_p(x+z) + \mathrm{lpNorm}_p(y+z) \;\le\; 2\,\rho_p\big(\mathrm{lpNorm}_p(x+y+z)\big).
--   $$
--
--   After normalizing the three singleton $p$-norms to sum to one, this bounds the sum of the three pairwise $p$-norms purely in terms of the norm of the total sum $x+y+z$. It supplies the total-norm-dependent estimate used to confine a hypothetical strict counterexample to the sharp diagonal Hlawka inequality to a narrow range of total norms.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/ScalarBounds.lean#L184-L228

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
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

theorem HlawkaSchatten.DiagonalConstruction.normalized_pair_sum_le {p : ℝ} (hp : 1 < p) (x y z : ι → ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1) :
    lpNorm p (x + y) + lpNorm p (x + z) + lpNorm p (y + z) ≤
      2 * scalarEnvelopeRoot p (lpNorm p (x + y + z)) := by sorry
