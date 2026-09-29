-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclic_denominator_pos
-- name    : HlawkaSchatten.DiagonalConstruction.cyclic_denominator_pos
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T17:25:17.703962+00:00
-- url     : https://prove2.me/theorems/dada5acf-489d-498e-a66f-2ba32a040c01
-- title:
--   Positivity of the cyclic ratio's denominator
-- statement:
--   For a real exponent $p$ and a real parameter $t\ge0$, define
--   $$
--   A_p(t) = \bigl(t^{p}+2\bigr)^{1/p}, \qquad B_p(t) = \bigl(2\,|1-t|^{p}+2^{p}\bigr)^{1/p}.
--   $$
--   These are, respectively, the common coordinate $p$-norm of each of the three vectors $(-t,1,1)$, $(1,-t,1)$, $(1,1,-t)$ in $\mathbb R^3$, and the common $p$-norm of each of their three pairwise sums.
--
--   For every real $p>1$ and every real $t\ge0$,
--   $$
--   0 \;<\; 6A_p(t) - 3B_p(t).
--   $$
--
--   The quantity $6A_p(t)-3B_p(t)$ is exactly the denominator of the cyclic ratio
--   $$
--   R_p(t) \;=\; \frac{3A_p(t)-3^{1/p}|2-t|}{6A_p(t)-3B_p(t)},
--   $$
--   whose supremum over $t\in[1/2,2]$ defines the cyclic candidate constant used elsewhere in the diagonal construction. Proving this denominator strictly positive, without assuming any form of Hlawka's inequality, is what lets $R_p$ be treated as an honest continuous real-valued function of $t$ on a compact interval.
--
--   **Formalization Note.** $A_p$ and $B_p$ are built from Lean's totalized real power `Real.rpow` at arbitrary real $p,t$; the hypothesis $t\ge0$ is what makes them literal coordinate $p$-norms of the vectors above (for $t<0$ the formula for $A_p(t)$ need not agree with $\|(-t,1,1)\|_p$).
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/Cyclic.lean#L50-L70

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# The cyclic comparison constant

The constant is defined from an explicit scalar formula on a fixed compact
interval. Its denominator is positive, so continuity gives an attained
maximum without presupposing the global Hlawka inequality.
-/

open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.cyclic_denominator_pos {p t : ℝ} (hp : 1 < p) (ht : 0 ≤ t) :
    0 < 6 * cyclicA p t - 3 * cyclicB p t := by sorry
