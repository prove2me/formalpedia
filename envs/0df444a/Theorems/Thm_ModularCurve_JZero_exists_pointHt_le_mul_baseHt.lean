-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_pointHt_le_mul_baseHt
-- name    : ModularCurve.JZero.exists_pointHt_le_mul_baseHt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/aefc1c5f-b877-5172-a697-c0af5601c0b0
-- title:
--   Point height bounded by (2g+1) times base height
-- statement:
--   Fix a level $N \ge 1$ and let $F =$ `modularFunctionFieldBar N` be the base change to $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` of the full modular function field of level $N$, realised as an intermediate field of the Laurent series field over $\overline{\mathbb Q}$. Let $r$ be a natural number and $s : \mathrm{Fin}\,r \to F$ a family satisfying `IsEmbBasis N s`, that is: $s$ is linearly independent over $\overline{\mathbb Q}$ and its range spans the Riemann–Roch space $\{f \in F : v(f) \le \exp(D\,v) \text{ for all places } v\}$ of the divisor $D =$ `embDivisor N` $= (2g+1)\,[\bar\infty]$, where $g =$ `genusFF` $\overline{\mathbb Q}\,F$ and $\bar\infty =$ `cuspInftyBar N` is the $q$-expansion place at infinity (the place attached to $j$). The assertion is the existence of a real constant $C$ (depending on $N$ and $s$ only) such that for every place $v$ of $F$ over $\overline{\mathbb Q}$ — a valuation subring containing $\overline{\mathbb Q}$, not all of $F$, and a principal ideal ring — with $v \ne \bar\infty$, one has
--   $$\mathrm{pointHt}_s(v) \le (2g+1)\,\mathrm{baseHt}_s(\bar\infty, v) + C,$$
--   where $\mathrm{pointHt}_s(v)$ is the absolute logarithmic Weil height of the $\overline{\mathbb Q}$-vector of residues $v(s_i/s_{\mathrm{pivot}})$, and, since $v \ne \bar\infty$, $\mathrm{baseHt}_s(\bar\infty, v) = \mathrm{pointHt}_s(v) + \mathrm{pointHt}_s(\bar\infty) - \mathrm{absLogHeight}(\mathrm{chordVec}\,s\,v\,\bar\infty)$.
--
--   This is the comparison, in the projective model of $X_0(N)$ afforded by a basis of $L((2g+1)\bar\infty)$, between the naive point height of a place and the bilinear base height against the cusp at infinity; it says the latter dominates the former up to the factor $2g+1$ and a bounded error. It is one of the positivity inputs for the height form on `JZero N`, and is used in the estimates bounding divisor naive heights by base mass and comparing the base mass with the height form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_pointHt_le_mul_baseHt.lean

import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.JZero.exists_pointHt_le_mul_baseHt (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ C : ℝ, ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v ≠ cuspInftyBar N →
      pointHt s v ≤ (embDegree N : ℝ) * baseHt s (cuspInftyBar N) v + C := by sorry
