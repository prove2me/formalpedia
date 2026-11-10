-- Prove2me | Theorems.Thm_LRTempElim_eq_135
-- name    : LRTempElim.eq_135
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:12.530013+00:00
-- url     : https://prove2.me/theorems/358dd5a8-d0df-41cc-ab3a-eba87600c1ee
-- title:
--   Eq. (135): $I_a=\frac{e^{-a^2/8}}{4\sqrt{2\pi}}\int x^2e^{-x^2/2}\operatorname{sech}(ax/2)\,dx$, $I_0=1/4$
-- statement:
--   Let $I_a=\mathbb E_{\nu_a}[X^2\sigma(aX)(1-\sigma(aX))]$ with $\nu_a=\tfrac12(N(a/2,1)+N(-a/2,1))$ and $\sigma(u)=1/(1+e^{-u})$. For every real $a$,
--   $$
--   I_a=\frac{e^{-a^2/8}}{4\sqrt{2\pi}}\int_{-\infty}^{\infty}x^2e^{-x^2/2}\operatorname{sech}\Big(\frac{ax}2\Big)\,dx,
--   $$
--   and $I_0=1/4$.
--
--   The integral representation is the starting point for the large-$a$ asymptotics (136) of the logistic slope information.
--
--   **Formalization Note** $\operatorname{sech}u=1/\cosh u$; the integral is a Lebesgue integral over $\mathbb R$.
--
--   Differences from the source:
--   - generalization: a ≥ 0 (the Gaussian setting of §B.3.3) → every real a; reason: both sides are even in a, so the identity for a ≥ 0 is the special case; §4.1 lets a be any real
--   - encoding: sech(ax/2) → (Real.cosh (a * x / 2))⁻¹; reason: definition of sech
-- source:
--   Chen, Wu, Yang, Zeng, Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee651394d60e9274fc77c5a1bd08841eb53ee6030924de85b47f5a195371758), §B.3.3, eq. (135), p.41 (pdf p.43)

import Mathlib
import Definitions.Def_LRTempElim_Logistic

open MeasureTheory ProbabilityTheory

namespace LRTempElim

/-- **Eq. (135)**: integral form of the logistic information. Chen, Wu, Yang, Zeng,
*Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination*, STOC 2027
submission (manuscript of 2026-11-03, sha256 eee65139…), §B.3.3, eq. (135), p.41 (pdf p.43).

"The information can be written as
`I_a = e^{−a²/8}/(4√(2π)) ∫_{−∞}^{∞} x² e^{−x²/2} sech(ax/2) dx`, (135) with `I₀ = 1/4`."

**Formalization Note.** `I_a = E_{ν_a}[X²σ(aX)(1 − σ(aX))]` with `ν_a = (P_a + Q_a)/2` (`Ia`;
§B.3.3's `ν` is the same `ν_a`). `sech u = 1/cosh u`, written `(Real.cosh u)⁻¹`. The integral is
over `ℝ` against Lebesgue measure. Stated for every real `a`. -/
theorem eq_135 :
    (∀ a : ℝ, Ia a = Real.exp (-a ^ 2 / 8) / (4 * Real.sqrt (2 * Real.pi)) *
        ∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2 / 2) * (Real.cosh (a * x / 2))⁻¹) ∧
      Ia 0 = 1 / 4 := by sorry

end LRTempElim
