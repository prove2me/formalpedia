-- Prove2me | Theorems.Thm_GoldieRenewal_Rates_contour_convolution_identity
-- name    : GoldieRenewal.Rates.contour_convolution_identity
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-06T03:45:45.136515+00:00
-- url     : https://prove2.me/theorems/9fcfa59f-33e2-4d6d-9eaf-98dbee80479d
-- title:
--   Proof of Theorem 3.2(i), pp. 154–155 — g₁ ∗ c(s) = (1/2π)∮ e^{−iθs} ĝ₁(θ)/(1 − η̂(θ)) dθ
-- statement:
--   Let $(\Omega,\mathcal A,P)$ be a probability space, $\kappa>0$, $\beta>0$, and let $M\ge0$ and $R$ be independent real random variables satisfying the hypotheses of Goldie's Theorem 3.2: $\mathbf E M^\kappa=1$ (2.3), $\mathbf E M^{\kappa+\beta}<\infty$ (3.3), the conditional law of $\log M$ given $M\ne0$ is spread out (3.4), and the tilted law $\eta(dx)=e^{\kappa x}P(\log M\in dx)$ satisfies (3.1) and the subsequent conditions of Theorem 3.1. Assume (3.7): $\int_0^\infty|P(R>t)-P(MR>t)|\,t^{\kappa+\beta-1}\,dt<\infty$. Let $\mathscr C$ be the positively oriented boundary of an axis-parallel rectangle contained in the strip $D=\{-\beta<\Im\theta<0\}$ whose interior contains every zero of $1-\hat\eta$ in $D$. Write $g_1(t)=e^{\kappa t}\big(P(R>e^t)-P(MR>e^t)\big)$ (3.5), $\hat g_1(\theta)=\int_{\mathbb R}e^{i\theta t}g_1(t)\,dt$, and
--   $$c(t)=\frac1{2\pi}\oint_{\mathscr C}\frac{e^{-i\theta t}}{1-\hat\eta(\theta)}\,d\theta .$$
--   Then for every $s\in\mathbb R$,
--   $$\int_{\mathbb R}g_1(u)\,c(s-u)\,du=\frac1{2\pi}\oint_{\mathscr C}e^{-i\theta s}\,\frac{\hat g_1(\theta)}{1-\hat\eta(\theta)}\,d\theta .$$
--
--   This identifies the convolution $g_1*c$ appearing in the remainder $r_1=C_+-r-(g_1*c)\mathbf 1_{t>0}$ of the proof of Theorem 3.2(i) with the contour term of the expansion (3.8), evaluated at $s=\log t$.
--
--   **Formalization Note** $c$ is `cFun`, $g_1$ is `gPos`, $\hat g_1$ is `fourierTransform` of $g_1$ (sign $+i$), $\hat\eta$ is `charTransform`; $\oint_{\mathscr C}$ is `RectangleIntegral` over the rectangle with corners $z$, $w$ (`EnclosesZerosInStrip`). Integrals over $\mathbb R$ are Bochner integrals.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, §9, proof of Theorem 3.2(i), pp. 154–155 (identification of g₁ ∗ c with the contour term of (3.8))

import Mathlib
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_GoldieRenewal_Rates_Transforms
import Definitions.Def_GoldieRenewal_Rates_Model
import Definitions.Def_GoldieRenewal_Rates_Expansion

open MeasureTheory ProbabilityTheory Complex

namespace GoldieRenewal.Rates

/-- **Contour form of `g₁ ∗ c`** (Goldie 1991, proof of Theorem 3.2(i), pp. 154–155,
identification of `g₁ ∗ c` with the contour term of (3.8)). Under the hypotheses of
Theorem 3.2 and (3.7), for an admissible rectangle contour `𝒞` and every `s ∈ ℝ`,
`∫ g₁(u) c(s − u) du = (1/2π) ∮_𝒞 e^{−iθs} ĝ₁(θ)/(1 − η̂(θ)) dθ`. -/
theorem contour_convolution_identity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (hM : Measurable M) (hR : Measurable R) (hM_nonneg : ∀ᵐ ω ∂P, 0 ≤ M ω)
    (h_indep : IndepFun R M P) (κ β : ℝ) (hκ : 0 < κ) (hβ : 0 < β)
    (h_2_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ κ) ∂P = 1)
    (h_3_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ (κ + β)) ∂P < ⊤)
    (h_3_4 : SpreadOut (logLawGivenNonzero P M))
    (h_stone : StoneConditions (tiltedLaw P M κ) β)
    (h_3_7 : IntegrableOn (fun t : ℝ =>
        (P.real {ω | t < R ω} - P.real {ω | t < M ω * R ω}) * t ^ (κ + β - 1)) (Set.Ioi 0))
    (z w : ℂ)
    (h_C : EnclosesZerosInStrip (fun θ => 1 - charTransform (tiltedLaw P M κ) θ) β z w) (s : ℝ) :
    ∫ u : ℝ, (gPos P M R κ u : ℂ) * cFun (tiltedLaw P M κ) z w (s - u) =
      (1 / (2 * Real.pi : ℂ)) *
        RectangleIntegral
          (fun θ : ℂ => Complex.exp (-(I * θ * (s : ℂ))) *
            fourierTransform (fun v => (gPos P M R κ v : ℂ)) θ /
              (1 - charTransform (tiltedLaw P M κ) θ)) z w := by sorry

end GoldieRenewal.Rates
