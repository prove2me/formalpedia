-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_scalar_window66
-- name    : HlawkaSchatten.DiagonalCutoff.scalar_window66
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-10T05:17:54.071789+00:00
-- url     : https://prove2.me/theorems/e58a73be-df69-4ac4-86f7-687e2417463c
-- title:
--   Scalar window for the cyclic constant on $66 \le p \le 70$
-- statement:
--   On the exponent interval from $66$ to $70$, the cyclic Hlawka constant lies strictly above the linear function $\frac{23}{50}p$ and strictly above the scalar envelope evaluated at confinement radius $\frac{73}{200}$, and it is at most $\frac{p}{2}$.
--
--   Let $C(p)$ denote the cyclic constant, the maximum of the explicit cyclic ratio on the interval $[\frac12,2]$. Let $E(p,q)$ denote the scalar envelope used to confine a hypothetical counterexample of total norm $q$. For every real $p$ with $66\le p\le 70$,
--
--   $$
--   \frac{23}{50}p < C(p),\qquad E\!\left(p,\frac{73}{200}\right) < C(p),\qquad C(p)\le \frac p2.
--   $$
--
--   These three bounds are the scalar input to the cutoff-$66$ localization and convexity arguments. The same confinement radius $\frac{73}{200}$ still sits below $C(p)$ at the left endpoint $p=66$.
--
--   **Formalization Note.** In Lean the cyclic constant is `cyclicConstant` and the envelope is `scalarEnvelope`.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — scalar confinement bounds for the cutoff-66 real estimate, with radius 73/200 and linear slope 23/50.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.scalar_window66 : ∀ p : ℝ, 66 ≤ p → p ≤ 70 →
    (23 / 50 : ℝ) * p < cyclicConstant p ∧
    scalarEnvelope p (73 / 200) < cyclicConstant p ∧
    cyclicConstant p ≤ p / 2 := by sorry
