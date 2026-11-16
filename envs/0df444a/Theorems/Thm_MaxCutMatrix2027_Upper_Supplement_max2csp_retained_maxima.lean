-- Prove2me | Theorems.Thm_MaxCutMatrix2027_Upper_Supplement_max2csp_retained_maxima
-- name    : MaxCutMatrix2027.Upper.Supplement.max2csp_retained_maxima
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:14:41.097173+00:00
-- url     : https://prove2.me/theorems/e20ecad8-cd57-4069-899f-a8e9961953ba
-- title:
--   Lemma A.5 — Sampling the retained MAX-2CSP part
-- statement:
--   Fix a MAX-2CSP instance $F$ on $n$ variables, a real $1\le s\le n$ and $0<\tau\le1$, and let $L$ and $P$ be as in Lemma A.3, with $B=16$. Then
--   $$\mathbb E\left[\left|\max_{z\in\mathcal X}\frac{z^TPLPz}{s^2}-\max_{z\in\mathcal X}\frac{z^TLz}{n^2}\right|\right]\le\frac{16B}{\sqrt s}+\frac{68B^2}{\tau s}.$$
--
--   Both maxima range over the full fractional set $\mathcal X$ and are attained, but not necessarily at integral points. The case with no retained eigenvalue ($L=0$) is included.
--
--   Differences from the source:
--   - encoding: vertices (variables) labelled by [n] → Fin n = {0,…,n−1}; reason: relabeling is bijective
--   - encoding: independent Bernoulli(s/n) selectors → the exact finite Bernoulli-subset expectation sampleAverage (s/n); reason: the subset weights are exactly the independent-selector law
-- source:
--   Songhua He, STOC 2027 submission #351 (October 2026), Lemma A.5, p.47 (PDF p.47); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/351.pdf; PDF SHA-256 b38cd84079663d9e2eb7375d7bf1572d5dc7c2157cfaf90e175fd371a9503631

import Definitions.Def_MaxCutMatrix2027_Upper_Supplement_CSP
import Definitions.Def_MaxCutMatrix2027_Upper_MatrixModel
set_option autoImplicit false

namespace MaxCutMatrix2027.Upper.Supplement

/-- Lemma A.5, p.47, with `B = 16` and the standing hypotheses of pp.42–43. Maxima range over
the full fractional set `X`. -/
theorem max2csp_retained_maxima (n : ℕ) (F : CSPInstance n) (s τ : ℝ)
    (hs : 1 ≤ s) (hsn : s ≤ n) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    let B : ℝ := 16
    sampleAverage (s / n) (fun Q =>
      |cspMax (cspRestrict Q (cspRetained F τ)) / s ^ 2 - cspMax (cspRetained F τ) / (n : ℝ) ^ 2|) ≤
      16 * B / Real.sqrt s + 68 * B ^ 2 / (τ * s) := by sorry

end MaxCutMatrix2027.Upper.Supplement
