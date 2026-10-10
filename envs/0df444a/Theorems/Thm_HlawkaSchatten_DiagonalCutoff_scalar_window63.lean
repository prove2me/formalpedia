-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_scalar_window63
-- name    : HlawkaSchatten.DiagonalCutoff.scalar_window63
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-10T07:14:55.159655+00:00
-- url     : https://prove2.me/theorems/432a194a-3c7e-4510-ae56-3d77949f59d3
-- title:
--   Scalar window for the cyclic constant on $63 \le p \le 64$
-- statement:
--   On the exponent interval from $63$ to $64$, the cyclic Hlawka constant lies strictly above $\frac{23}{50}p$ and strictly above the scalar envelope at confinement radius $\frac{91}{250}$, and it is at most $\frac{p}{2}$.
--
--   For every real $p$ with $63\le p\le 64$,
--
--   $$
--   \frac{23}{50}p < C(p),\qquad E\!\left(p,\frac{91}{250}\right) < C(p),\qquad C(p)\le \frac p2.
--   $$
--
--   The radius $\frac{91}{250}$ still lies inside this one-integer window. These three bounds are the scalar input to the cutoff-$63$ localization and convexity arguments.
--
--   **Formalization Note.** In Lean the cyclic constant is `cyclicConstant` and the envelope is `scalarEnvelope`.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — scalar confinement at radius 91/250 for the cutoff-63 real estimate.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.scalar_window63 : ∀ p : ℝ, 63 ≤ p → p ≤ 64 →
    (23 / 50 : ℝ) * p < cyclicConstant p ∧
    scalarEnvelope p (91 / 250) < cyclicConstant p ∧
    cyclicConstant p ≤ p / 2 := by sorry
