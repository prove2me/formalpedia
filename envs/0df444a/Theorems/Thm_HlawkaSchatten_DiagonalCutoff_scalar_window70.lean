-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_scalar_window70
-- name    : HlawkaSchatten.DiagonalCutoff.scalar_window70
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-10T04:14:53.807505+00:00
-- url     : https://prove2.me/theorems/e82936c8-1a4c-458e-95d4-905ca01cc949
-- title:
--   Scalar window for the cyclic constant on 70 ≤ p ≤ 80
-- statement:
--   On the exponent interval from $70$ to $80$, the cyclic Hlawka constant lies strictly above the linear function $\frac{23}{50}p$ and strictly above the scalar envelope evaluated at confinement radius $\frac{73}{200}$, and it is at most $\frac{p}{2}$.
--
--   Let $C(p)$ denote the cyclic constant, the maximum of the explicit cyclic ratio on the interval $[\frac12,2]$. Let $E(p,q)$ denote the scalar envelope used to confine a hypothetical counterexample of total norm $q$. For every real $p$ with $70\le p\le 80$,
--
--   $$
--   \frac{23}{50}p < C(p),\qquad E\!\left(p,\frac{73}{200}\right) < C(p),\qquad C(p)\le \frac p2.
--   $$
--
--   These three bounds are the scalar input to the cutoff-$70$ localization and convexity arguments. The confinement radius $\frac{73}{200}$ is the value at which the envelope still sits below $C(p)$ at the left endpoint $p=70$.
--
--   **Formalization Note.** In Lean the cyclic constant is `cyclicConstant` and the envelope is `scalarEnvelope`.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — scalar confinement bounds used by the cutoff-70 real estimate, with radius 73/200 and linear slope 23/50.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.scalar_window70 : ∀ p : ℝ, 70 ≤ p → p ≤ 80 →
    (23 / 50 : ℝ) * p < cyclicConstant p ∧
    scalarEnvelope p (73 / 200) < cyclicConstant p ∧
    cyclicConstant p ≤ p / 2 := by sorry
