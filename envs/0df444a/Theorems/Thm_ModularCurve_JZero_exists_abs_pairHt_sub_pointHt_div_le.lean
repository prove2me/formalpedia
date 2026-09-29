-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_abs_pairHt_sub_pointHt_div_le
-- name    : ModularCurve.JZero.exists_abs_pairHt_sub_pointHt_div_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/8e7098c5-f4d9-564d-b5d2-1cf0c785e9ed
-- title:
--   Pair height against a fixed place, up to ε h
-- statement:
--   Let $N\ge 1$ and let $\bar F_N$ denote `modularFunctionFieldBar N`, the intermediate field of $\overline{\mathbb Q}$ inside the Laurent series field $\overline{\mathbb Q}((q))$ obtained by base change of `modularFunctionFieldFull N` to $\overline{\mathbb Q}$; places are valuation subrings of $\bar F_N$ containing the image of $\overline{\mathbb Q}$, distinct from the whole field and with principal ideals. Let $r\in\mathbb N$ and $s\colon \mathrm{Fin}\,r\to\bar F_N$ satisfy `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and spans the Riemann–Roch space of the divisor $(2g+1)\,\bar\infty$, where $\bar\infty$ is `cuspInftyBar N`, $g=$ `genusFF` $=\dim_{\overline{\mathbb Q}} H^1(0)$ and $2g+1=$ `embDegree N`. Here, for a place $v$, `evalVec s v` is the tuple of residues $v(s_i s_{i_0}^{-1})$ at a pivot index $i_0$, `pointHt s v` is the absolute logarithmic height of that tuple (its logarithmic height divided by the degree over $\mathbb Q$ of the field its entries generate), `chordVec s v w` is the family of $2\times 2$ minors $\mathrm{ev}_v(i)\mathrm{ev}_w(j)-\mathrm{ev}_v(j)\mathrm{ev}_w(i)$, and `pairHt s v w` $=$ `pointHt s v` $+$ `pointHt s w` $-$ the absolute logarithmic height of `chordVec s v w`. Then for every real $\varepsilon>0$ and every place $w_0$ there is a real constant $C$ such that for all places $u$ with $u\ne w_0$ and $u\ne\bar\infty$, $$\bigl|\,\mathrm{pairHt}\,s\,u\,w_0-\tfrac{1}{2g+1}\,\mathrm{pointHt}\,s\,u\,\bigr|\le \varepsilon\,\mathrm{pointHt}\,s\,u+C.$$
--
--   This is the height-machine comparison, on the projective model of $X_0(N)$ over $\overline{\mathbb Q}$ furnished by a basis of $L((2g+1)\bar\infty)$, between the pair (chord) height against a fixed place $w_0$ and the point height scaled by $1/(2g+1)$: the two arise from complete linear systems of equal degree, so they agree up to $\varepsilon h+C$, the $\varepsilon$ being unavoidable since $w_0$ and $\bar\infty$ are only numerically equivalent. It is used downstream in the estimates [`ModularCurve.JZero.exists_absLogHeight_regVal_sub_two_mul_pointHt_le`](thm.html#ModularCurve.JZero.exists_absLogHeight_regVal_sub_two_mul_pointHt_le) and [`ModularCurve.JZero.exists_sub_mul_baseHt_le_pairHt`](thm.html#ModularCurve.JZero.exists_sub_mul_baseHt_le_pairHt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_abs_pairHt_sub_pointHt_div_le.lean

import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.exists_abs_pairHt_sub_pointHt_div_le (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (ε : ℝ) (hε : 0 < ε)
    (w₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    ∃ C : ℝ, ∀ u : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      u ≠ w₀ → u ≠ cuspInftyBar N →
        |pairHt s u w₀ - pointHt s u / (embDegree N : ℝ)| ≤ ε * pointHt s u + C := by sorry
