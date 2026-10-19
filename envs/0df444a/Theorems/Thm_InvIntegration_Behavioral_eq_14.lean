-- Prove2me | Theorems.Thm_InvIntegration_Behavioral_eq_14
-- name    : InvIntegration.Behavioral.eq_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:08.772+00:00
-- url     : https://prove2.me/theorems/b3f28a9e-7d0b-4f65-825d-32ae5bc5c96e
-- title:
--   Eq. (14), EC p. 3 (PDF 35) — ξ = cv · E[min(B(ẑ − X)⁺, X + 1/cv)], X ∼ N(0,1)
-- statement:
--   Let $(q,v,\xi)$ be an equilibrium of a market $N(m,\mathrm{sd}^2)$ with $m>0$, $\mathrm{sd}>0$, coefficient of variation $cv=\mathrm{sd}/m$, and let
--   $$B = \frac{\bar G(v)}{G(v)-G(s/\delta)}$$
--   be the ratio of first-period to second-period demand. Then, with $X\sim N(0,1)$,
--   $$\xi = cv\cdot\mathbb E_X\Bigl[\min\Bigl(B(\hat z-X)^+,\ X+\frac{1}{cv}\Bigr)\Bigr]. \tag{14}$$
--
--   This is the fixed-point equation for the second-period fill rate on which the proof of Proposition 5 rests.
--
--   **Formalization Note.** The page writes $B(\xi)$ evaluated at $(p-\xi s)/(1-\xi\delta)$; here $B$ is evaluated at the equilibrium valuation $v$. The two agree when $\xi\ge 0$ (by (8)); when $\xi<0$ the equilibrium valuation is $p$, not $(p-\xi s)/(1-\xi\delta)$.
-- source:
--   Aflaki & Swinney, Inventory Integration with Rational Consumers, SSRN preprint 2842182 (July 2020), EC p. 3 (PDF 35), proof of Proposition 5, eq. (14)

import Mathlib
import Definitions.Def_InvIntegration_Behavioral_Model

namespace InvIntegration.Behavioral

open MeasureTheory ProbabilityTheory in
theorem eq_14 (P : Params) (hS : P.Standing) (m sd : ℝ) (hm : 0 < m) (hsd : 0 < sd)
    (q v ξ : ℝ) (hE : IsEquilibrium P m sd q v ξ) :
    ξ = sd / m * ∫ x, min (Gbar P v / (G P v - G P (P.s / P.δ)) * max (P.zh - x) 0) (x + m / sd)
      ∂ gaussianReal 0 1 := by sorry

end InvIntegration.Behavioral
