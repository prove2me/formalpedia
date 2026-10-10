-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_scalar_window65
-- name    : HlawkaSchatten.DiagonalCutoff.scalar_window65
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-10T06:02:23.657657+00:00
-- url     : https://prove2.me/theorems/8cd704a2-c837-4d57-bbe2-b15657beeeec
-- title:
--   Scalar window for the cyclic constant on $65 \le p \le 66$
-- statement:
--   On the exponent interval from $65$ to $66$, the cyclic Hlawka constant lies strictly above the linear function $\frac{23}{50}p$ and strictly above the scalar envelope evaluated at confinement radius $\frac{91}{250}$, and it is at most $\frac{p}{2}$.
--
--   Let $C(p)$ denote the cyclic constant, the maximum of the explicit cyclic ratio on the interval $[\frac12,2]$. Let $E(p,q)$ denote the scalar envelope used to confine a hypothetical counterexample of total norm $q$. For every real $p$ with $65\le p\le 66$,
--
--   $$
--   \frac{23}{50}p < C(p),\qquad E\!\left(p,\frac{91}{250}\right) < C(p),\qquad C(p)\le \frac p2.
--   $$
--
--   These three bounds are the scalar input to the cutoff-$65$ localization and convexity arguments. The confinement radius $\frac{91}{250}$ is the value at which the scalar model and the Hessian power comparison both close on this one-integer window.
--
--   **Formalization Note.** In Lean the cyclic constant is `cyclicConstant` and the envelope is `scalarEnvelope`.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — scalar confinement at radius 91/250 for the cutoff-65 real estimate.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.scalar_window65 : ∀ p : ℝ, 65 ≤ p → p ≤ 66 →
    (23 / 50 : ℝ) * p < cyclicConstant p ∧
    scalarEnvelope p (91 / 250) < cyclicConstant p ∧
    cyclicConstant p ≤ p / 2 := by sorry
