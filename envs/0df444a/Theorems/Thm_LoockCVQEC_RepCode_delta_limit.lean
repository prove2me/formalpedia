-- Prove2me | Theorems.Thm_LoockCVQEC_RepCode_delta_limit
-- name    : LoockCVQEC.RepCode.delta_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:12.331965+00:00
-- url     : https://prove2.me/theorems/5ce1c8ee-6f0a-4be0-aaab-da66b712e817
-- title:
--   Sec. IV, p. 4 — as r → ∞ the squeezed-ancilla marginals in Eq. (9) become delta functions
-- statement:
--   Let $m_r(y)=\sqrt{2/(\pi e^{-2r})}\,e^{-2e^{2r}y^2}$ be the x-marginal of the squeezed ancilla (a centred Gaussian density of variance $e^{-2r}/4$). Let $h:\mathbb R^2\to\mathbb R$ be bounded, measurable and continuous at $c=(c_2,c_3)$. Then
--   $$\lim_{r\to\infty}\int_{\mathbb R^2}m_r(y_2-c_2)\,m_r(y_3-c_3)\,h(y_2,y_3)\,dy_2\,dy_3=h(c).$$
--
--   This is the precise meaning of the paper's sentence that "the Gaussian distribution functions in Eq. (9) become delta functions" in the limit of infinite squeezing; it is the step that turns Eq. (9) into Eq. (10).
--
--   **Formalization Note** The integral is the Bochner integral over $\mathbb R\times\mathbb R$; boundedness and measurability of $h$ are the hypotheses under which the limit holds (they are met by the integrands arising from Eq. (9) with a measurable feedforward).
--
--   Differences from the source:
--   - reading: "the Gaussian distribution functions in Eq. (9) become delta functions" as r → ∞ → for every bounded measurable h continuous at c, ∫ m_r(y₂ − c₂) m_r(y₃ − c₃) h(y) dy → h(c) as r → ∞; reason: the standard meaning of convergence to a delta function; the integrands of Eq. (9) with a measurable feedforward meet these hypotheses
-- source:
--   van Loock, A note on quantum error correction with continuous variables, arXiv:0811.3616v1, p. 4, Sec. IV, before Eq. (10)

import Mathlib
import Definitions.Def_LoockCVQEC_RepCode_Protocol

namespace LoockCVQEC.RepCode

open Real MeasureTheory Filter Topology

theorem delta_limit (h : ℝ × ℝ → ℝ) (c : ℝ × ℝ) (hmeas : Measurable h)
    (hbdd : ∃ C : ℝ, ∀ y, |h y| ≤ C) (hcont : ContinuousAt h c) :
    Tendsto (fun r : ℝ => ∫ y : ℝ × ℝ, sqzMarg r (y.1 - c.1) * sqzMarg r (y.2 - c.2) * h y)
      atTop (𝓝 (h c)) := by sorry

end LoockCVQEC.RepCode
