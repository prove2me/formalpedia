-- Prove2me | Theorems.Thm_GoldieRenewal_Rates_eq_9_24
-- name    : GoldieRenewal.Rates.eq_9_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:41.886298+00:00
-- url     : https://prove2.me/theorems/616476e7-9152-458c-9b9d-6737153c22ce
-- title:
--   (9.24), proof of Theorem 3.2 — K ∗ ℜr₁(t) = o(e^{−βt}), t → ∞
-- statement:
--   Assume the hypotheses of Theorem 3.2 (with $\eta$ satisfying (3.1) and the subsequent conditions of Theorem 3.1) and (3.7). Let $b>\beta$, $K(t)=be^{-bt}\mathbf 1_{t>0}$, $r(t)=e^{\kappa t}P(R>e^t)$, let $\mathscr C$ be the positively oriented boundary of an admissible rectangle, and
--   $$c(t)=\frac1{2\pi}\oint_{\mathscr C}e^{-i\theta t}\frac{d\theta}{1-\hat\eta(\theta)},\qquad r_1(t)=C_+-r(t)-(g_1*c)(t)\mathbf 1_{t>0}.$$
--   Then
--   $$K*\Re r_1(t)=o(e^{-\beta t}),\qquad t\to\infty .$$
--
--   This is the smoothed form of the rate in Theorem 3.2(i); the Tauberian remainder theorem (Theorem 9.6) removes the smoothing at the cost of halving the exponent.
--
--   **Formalization Note** $K*f(t)=\int K(t-u)f(u)\,du$ and $(g_1*c)(t)=\int g_1(u)c(t-u)\,du$. (3.7) is read with $P(R>t)$ in place of the printed $P(R>-t)$.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, §9, proof of Theorem 3.2(i), (9.24), p. 154

import Mathlib
import Definitions.Def_GoldieRenewal_Rates_Transforms
import Definitions.Def_GoldieRenewal_Rates_Model
import Definitions.Def_GoldieRenewal_Rates_Expansion

open MeasureTheory ProbabilityTheory Filter Asymptotics

namespace GoldieRenewal.Rates

/-- **(9.24)** (Goldie 1991, proof of Theorem 3.2(i), p. 154). Under the hypotheses of
Theorem 3.2 and (3.7), with `K(t) = b e^{−bt} 1_{t>0}` for a constant `b > β`,
`c(t) = (1/2π) ∮_𝒞 e^{−iθt} dθ/(1 − η̂(θ))` and `r₁(t) = C₊ − r(t) − g₁ ∗ c(t) 1_{t>0}`:
`K ∗ ℜr₁(t) = o(e^{−βt})`, `t → ∞`.
Formalization Note: `𝒞` is any admissible positively oriented rectangle boundary
(`EnclosesZerosInStrip`); `K ∗ f(t) = ∫ K(t − u) f(u) du`, `g₁ ∗ c(t) = ∫ g₁(u) c(t − u) du`.
(3.7) is read with `P(R > t)`. -/
theorem eq_9_24 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (hM : Measurable M) (hR : Measurable R) (hM_nonneg : ∀ᵐ ω ∂P, 0 ≤ M ω)
    (h_indep : IndepFun R M P) (κ β : ℝ) (hκ : 0 < κ) (hβ : 0 < β)
    (h_2_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ κ) ∂P = 1)
    (h_3_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ (κ + β)) ∂P < ⊤)
    (h_3_4 : SpreadOut (logLawGivenNonzero P M))
    (h_stone : StoneConditions (tiltedLaw P M κ) β)
    (h_3_7 : IntegrableOn (fun t : ℝ =>
        (P.real {ω | t < R ω} - P.real {ω | t < M ω * R ω}) * t ^ (κ + β - 1)) (Set.Ioi 0))
    (b : ℝ) (hb : β < b) (z w : ℂ)
    (h_C : EnclosesZerosInStrip (fun θ => 1 - charTransform (tiltedLaw P M κ) θ) β z w) :
    (fun t : ℝ => ∫ u : ℝ, smoothingKernel b (t - u) * (r1Fun P M R κ z w u).re)
      =o[atTop] (fun t : ℝ => Real.exp (-(β * t))) := by sorry

end GoldieRenewal.Rates
