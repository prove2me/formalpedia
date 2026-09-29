-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclicConstant_gt_separator
-- name    : HlawkaSchatten.DiagonalConstruction.cyclicConstant_gt_separator
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T18:32:24.917201+00:00
-- url     : https://prove2.me/theorems/2ba9390d-8f36-48fb-b322-b781a58cc41a
-- title:
--   A linear lower bound $\tfrac{939}{2000}p<K_p$ for the cyclic candidate constant
-- statement:
--   For a real exponent $p$ and $t\ge0$, let $A_p(t)=(t^p+2)^{1/p}$, $B_p(t)=(2|1-t|^p+2^p)^{1/p}$; let
--   $$
--   R_p(t) \;=\; \frac{3A_p(t)-3^{1/p}|2-t|}{6A_p(t)-3B_p(t)}
--   $$
--   be the cyclic ratio, and let
--   $$
--   K_p \;=\; \sup\{\,R_p(t) : 1/2\le t\le2\,\}
--   $$
--   be the cyclic candidate constant.
--
--   The theorem states that for every real $p\ge256$,
--   $$
--   \frac{939}{2000}\,p \;<\; K_p.
--   $$
--
--   It shows that $K_p$ grows at least linearly in $p$, with an explicit rational slope. Elsewhere in the diagonal construction, after a hypothetical failure of the $K_p$-Hlawka inequality has been relabeled so its total norm is the largest of the four vectors involved and rescaled so its three singleton norms sum to one, this lower bound on $K_p$ is compared against a matching upper bound (from a separate scalar-envelope estimate) at the reference value $53/150$; that comparison is what confines such a rescaled failure's total norm below $53/150$.
--
--   **Formalization Note.** The proof evaluates $R_p$ at the parameter `constructionParameter p := Real.exp (-(Real.log p * p⁻¹))`, i.e. $t^*=\exp(-\log(p)/p)=p^{-1/p}$ for $p>0$; for $p\ge256$ it satisfies $1/2\le t^*\le1$, so in particular $t^*\ge0$, and for $t\ge0$ the quantities $A_p(t)$ and $B_p(t)$ are the coordinate $p$-norms of each of the cyclic vectors $(-t,1,1),(1,-t,1),(1,1,-t)\in\mathbb R^3$ and of each of their pairwise sums.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/TailEstimates.lean#L153-L169

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
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

/-!
# Explicit uniform estimates above the cutoff

Rational logarithm bounds separate the cyclic witness and scalar envelope
at the common intermediate value `939 * p / 2000`.
-/

open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.cyclicConstant_gt_separator {p : ℝ} (hp : 256 ≤ p) :
    (939 / 2000 : ℝ) * p < cyclicConstant p := by sorry
