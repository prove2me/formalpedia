-- Prove2me | Theorems.Thm_OptimalPAC_SampleComplexity_log_technical
-- name    : OptimalPAC.SampleComplexity.log_technical
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:27:23.897697+00:00
-- url     : https://prove2.me/theorems/f794df1e-1268-48bc-8381-6704bf5cd1aa
-- title:
--   Lemma 5 — $a\ln(c_1(c_2+b/a))\le a\ln(c_1(c_2+e))+b/e$
-- statement:
--   For all real numbers $a,b,c_1\in[1,\infty)$ and $c_2\in[0,\infty)$,
--   $$a\ln\left(c_1\left(c_2+\frac ba\right)\right)\le a\ln\big(c_1(c_2+e)\big)+\frac1e\,b.$$
--
--   This elementary inequality converts the logarithmic factor in the proof of Theorem 2 into a sum of a term linear in $d$ and a term linear in $\ln(18/\delta)$ (the last step of the chain ending in (8)).
-- source:
--   Hanneke, The Optimal Sample Complexity of PAC Learning, arXiv:1507.00473v4, p. 13, Appendix A, Lemma 5

import Mathlib

namespace OptimalPAC.SampleComplexity

/-- **Lemma 5** (Hanneke 2016, Appendix A, p. 13): for `a, b, c₁ ≥ 1` and `c₂ ≥ 0`,
`a ln(c₁(c₂ + b/a)) ≤ a ln(c₁(c₂ + e)) + b/e`. -/
theorem log_technical (a b c₁ c₂ : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc₁ : 1 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    a * Real.log (c₁ * (c₂ + b / a)) ≤
      a * Real.log (c₁ * (c₂ + Real.exp 1)) + 1 / Real.exp 1 * b := by sorry

end OptimalPAC.SampleComplexity
