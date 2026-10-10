-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_scalar_window62
-- name    : HlawkaSchatten.DiagonalCutoff.scalar_window62
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-10T07:38:36.952253+00:00
-- url     : https://prove2.me/theorems/b0ed5e95-6c08-4d5f-9cec-2f6ea187245c
-- title:
--   Scalar window for the cyclic constant on $62 \le p \le 63$
-- statement:
--   On the exponent interval from $62$ to $63$, the cyclic Hlawka constant lies strictly above $\frac{23}{50}p$ and strictly above the scalar envelope at confinement radius $\frac{3643}{10000}$, and it is at most $\frac{p}{2}$.
--
--   For every real $p$ with $62\le p\le 63$,
--
--   $$
--   \frac{23}{50}p < C(p),\qquad E\!\left(p,\frac{3643}{10000}\right) < C(p),\qquad C(p)\le \frac p2.
--   $$
--
--   The radius $\frac{3643}{10000}$ lies inside this one-integer window. These three bounds are the scalar input to the cutoff-$62$ localization and convexity arguments.
--
--   **Formalization Note.** In Lean the cyclic constant is `cyclicConstant` and the envelope is `scalarEnvelope`.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — scalar confinement at radius 3643/10000 for the cutoff-62 real estimate.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.scalar_window62 : ∀ p : ℝ, 62 ≤ p → p ≤ 63 →
    (23 / 50 : ℝ) * p < cyclicConstant p ∧
    scalarEnvelope p (3643 / 10000) < cyclicConstant p ∧
    cyclicConstant p ≤ p / 2 := by sorry
