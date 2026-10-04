-- Prove2me | Theorems.Thm_NumStochOpt_Bounds_eq_2_51_simple_recourse_expected_cost
-- name    : NumStochOpt.Bounds.eq_2_51_simple_recourse_expected_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T19:18:57.656227+00:00
-- url     : https://prove2.me/theorems/8a6feb52-e544-485b-8b3e-02dc3e499298
-- title:
--   Eq. (2.51) — the expected simple-recourse cost in closed form
-- statement:
--   Let $h_j$ be an integrable real random variable on a probability space $(\Omega,P)$, let $\chi_j\in\mathbb R$, and let $q_j^+,q_j^-$ satisfy $q_j^++q_j^-\ge0$. With $Q_j$ the simple-recourse cost of p. 53, the probabilities $p_j^+(\chi_j)=P\{h_j\ge\chi_j\}$, $p_j^-(\chi_j)=P\{h_j<\chi_j\}$ and the conditional means $h_j^+(\chi_j)=E\{h_j\mid h_j\ge\chi_j\}$, $h_j^-(\chi_j)=E\{h_j\mid h_j<\chi_j\}$,
--   $$
--   EQ_j(\chi_j,h_j(\omega))=q_j^+\big(h_j^+(\chi_j)-\chi_j\big)p_j^+(\chi_j)+q_j^-\big(\chi_j-h_j^-(\chi_j)\big)p_j^-(\chi_j). \tag{2.51}
--   $$
--
--   The formula requires only one-dimensional integrals, so the objective of a simple-recourse problem can be evaluated exactly.
--
--   **Formalization Note** If $p_j^\pm(\chi_j)=0$ the conditional mean is undefined in the book; in Lean it is $0$, and the corresponding term vanishes, as it must. $h_j$ is assumed measurable and integrable.
-- source:
--   P. Kall, A. Ruszczyński, K. Frauendorfer, "Approximation Techniques in Stochastic Programming", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 2, p. 53, Eq. (2.51)

import Mathlib
import Definitions.Def_NumStochOpt_Bounds_SimpleRecourse

open MeasureTheory

namespace NumStochOpt.Bounds

/-- Eq. (2.51), p. 53: for an integrable random right-hand side `h_j` and `q⁺_j + q⁻_j ≥ 0`,
`E Q_j(χ_j, h_j) = q⁺_j (h⁺_j(χ_j) − χ_j) p⁺_j(χ_j) + q⁻_j (χ_j − h⁻_j(χ_j)) p⁻_j(χ_j)`. -/
theorem eq_2_51_simple_recourse_expected_cost {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hj : Ω → ℝ) (hmeas : Measurable hj)
    (hint : Integrable hj P) (qp qm : ℝ) (hq : 0 ≤ qp + qm) (χ : ℝ) :
    ∫ ω, simpleRecourseCost qp qm χ (hj ω) ∂P =
      qp * (condMeanAbove P hj χ - χ) * probAbove P hj χ +
        qm * (χ - condMeanBelow P hj χ) * probBelow P hj χ := by sorry

end NumStochOpt.Bounds
