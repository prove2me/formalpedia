-- Prove2me | Theorems.Thm_MaxCutMatrix2027_Upper_Supplement_max2csp_expected_sampling_error
-- name    : MaxCutMatrix2027.Upper.Supplement.max2csp_expected_sampling_error
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:15:07.7931+00:00
-- url     : https://prove2.me/theorems/55e7556a-c00d-41ef-8cbf-2afa6eacd7da
-- title:
--   Theorem A.2 (companion theorem) — Expected MAX-2CSP sampling error
-- statement:
--   There is an absolute constant $C_0>0$ such that for every MAX-2CSP instance $F$ on $n$ variables and every real $1\le s\le n$, if each variable is included in $Q$ independently with probability $s/n$, then
--   $$\mathbb E\left[\left|\frac{\mathrm{OPT}(F[Q])}{s^2}-\frac{\mathrm{OPT}(F)}{n^2}\right|\right]\le\frac{C_0}{\sqrt s}.$$
--
--   The normalization is by $s^2$, not $|Q|^2$; empty and singleton samples have optimum zero. This is the MAX-2CSP sampling theorem behind Algorithm 2.
--
--   Differences from the source:
--   - encoding: vertices (variables) labelled by [n] → Fin n = {0,…,n−1}; reason: relabeling is bijective
--   - encoding: independent Bernoulli(s/n) selectors → the exact finite Bernoulli-subset expectation sampleAverage (s/n); reason: the subset weights are exactly the independent-selector law
-- source:
--   Songhua He, STOC 2027 submission #351 (October 2026), Theorem A.2, p.42 (PDF p.42); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/351.pdf; PDF SHA-256 b38cd84079663d9e2eb7375d7bf1572d5dc7c2157cfaf90e175fd371a9503631

import Definitions.Def_MaxCutMatrix2027_Upper_Supplement_CSP
import Definitions.Def_MaxCutMatrix2027_Upper_MatrixModel
set_option autoImplicit false

namespace MaxCutMatrix2027.Upper.Supplement

/-- Theorem A.2, p.42. Real expected sample size `s`, uncapped independent variable sample,
normalization by `s²` and `n²`. -/
theorem max2csp_expected_sampling_error :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (n : ℕ) (F : CSPInstance n) (s : ℝ), 1 ≤ s → s ≤ n →
      sampleAverage (s / n) (fun Q => |(F.induced Q).optR / s ^ 2 - F.optR / (n : ℝ) ^ 2|) ≤
        C₀ / Real.sqrt s := by sorry

end MaxCutMatrix2027.Upper.Supplement
