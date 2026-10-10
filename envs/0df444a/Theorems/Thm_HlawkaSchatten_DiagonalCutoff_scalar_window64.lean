-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_scalar_window64
-- name    : HlawkaSchatten.DiagonalCutoff.scalar_window64
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-10T06:52:21.296979+00:00
-- url     : https://prove2.me/theorems/e1f9f1c4-5f80-4c53-8246-315f050da70c
-- title:
--   Scalar window for the cyclic constant on $64 \le p \le 65$
-- statement:
--   On the exponent interval from $64$ to $65$, the cyclic Hlawka constant lies strictly above the linear function $\frac{23}{50}p$ and strictly above the scalar envelope evaluated at confinement radius $\frac{91}{250}$, and it is at most $\frac{p}{2}$.
--
--   Let $C(p)$ denote the cyclic constant, the maximum of the explicit cyclic ratio on the interval $[\frac12,2]$. Let $E(p,q)$ denote the scalar envelope used to confine a hypothetical counterexample of total norm $q$. For every real $p$ with $64\le p\le 65$,
--
--   $$
--   \frac{23}{50}p < C(p),\qquad E\!\left(p,\frac{91}{250}\right) < C(p),\qquad C(p)\le \frac p2.
--   $$
--
--   These three bounds are the scalar input to the cutoff-$64$ localization and convexity arguments. The confinement radius $\frac{91}{250}$ is the same radius already used at cutoff $65$; it still sits inside the one-integer window at $64$.
--
--   **Formalization Note.** In Lean the cyclic constant is `cyclicConstant` and the envelope is `scalarEnvelope`.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — scalar confinement at radius 91/250 for the cutoff-64 real estimate.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.scalar_window64 : ∀ p : ℝ, 64 ≤ p → p ≤ 65 →
    (23 / 50 : ℝ) * p < cyclicConstant p ∧
    scalarEnvelope p (91 / 250) < cyclicConstant p ∧
    cyclicConstant p ≤ p / 2 := by sorry
