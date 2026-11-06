-- Prove2me | Theorems.Thm_GoldieRenewal_Rates_r1_bounded_tauberian
-- name    : GoldieRenewal.Rates.r1_bounded_tauberian
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-06T03:45:34.044564+00:00
-- url     : https://prove2.me/theorems/072e2bbe-cc66-40e6-a38c-4b47546937ac
-- title:
--   Proof of Theorem 3.2(i), pp. 154–155 — ℜr₁ is bounded, measurable and satisfies the Tauberian condition (9.25) with p = 1
-- statement:
--   Let $(\Omega,\mathcal A,P)$ be a probability space, $\kappa>0$, $\beta>0$, and let $M\ge0$ and $R$ be independent real random variables satisfying the hypotheses of Goldie's Theorem 3.2: $\mathbf E M^\kappa=1$ (2.3), $\mathbf E M^{\kappa+\beta}<\infty$ (3.3), the conditional law of $\log M$ given $M\ne0$ is spread out (3.4), and the tilted law $\eta(dx)=e^{\kappa x}P(\log M\in dx)$ satisfies (3.1) and the subsequent conditions of Theorem 3.1. Assume (3.7): $\int_0^\infty|P(R>t)-P(MR>t)|\,t^{\kappa+\beta-1}\,dt<\infty$. Let $\mathscr C$ be the positively oriented boundary of an axis-parallel rectangle contained in the strip $D=\{-\beta<\Im\theta<0\}$ whose interior contains every zero of $1-\hat\eta$ in $D$. Write $g_1(t)=e^{\kappa t}\big(P(R>e^t)-P(MR>e^t)\big)$ (3.5), $\hat g_1(\theta)=\int_{\mathbb R}e^{i\theta t}g_1(t)\,dt$, and
--   $$c(t)=\frac1{2\pi}\oint_{\mathscr C}\frac{e^{-i\theta t}}{1-\hat\eta(\theta)}\,d\theta .$$
--   Let $r(t)=e^{\kappa t}P(R>e^t)$ and $r_1(t)=C_+-r(t)-(g_1*c)(t)\,\mathbf 1_{t>0}$, where $(g_1*c)(t)=\int_{\mathbb R}g_1(u)c(t-u)\,du$ and $C_+$ is the constant (2.12). Then $f:=\Re r_1$ is measurable and bounded on $\mathbb R$, and there are constants $A$, $x_0$ such that the Tauberian condition (9.25) of Theorem 9.6 holds with $p=1$:
--   $$f(x)-f(x+y)\le A\,e^{-\beta x/2},\qquad 0\le y\le e^{-\beta x/2},\ x>x_0 .$$
--
--   These are the hypotheses on $f$ under which the Beurling–Ganelius Tauberian remainder theorem (Theorem 9.6, with the kernel $K(t)=be^{-bt}\mathbf 1_{t>0}$, for which one may take $p=1$) turns (9.24), $K*\Re r_1(t)=o(e^{-\beta t})$, into $\Re r_1(t)=O(e^{-\beta t/2})$ in the proof of Theorem 3.2(i).
--
--   **Formalization Note** $r_1$ is `r1Fun`, $c$ is `cFun`, $g_1$ is `gPos`; the contour is described by `EnclosesZerosInStrip` and `RectangleIntegral`. The exponent $-\beta x/(p+1)$ of (9.25) is written with $p=1$.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, §9, proof of Theorem 3.2(i), pp. 154–155 (verification of the hypotheses of Theorem 9.6 for ℜr₁)

import Mathlib
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_GoldieRenewal_Rates_Transforms
import Definitions.Def_GoldieRenewal_Rates_Model
import Definitions.Def_GoldieRenewal_Rates_Expansion

open MeasureTheory ProbabilityTheory Complex

namespace GoldieRenewal.Rates

/-- **Hypotheses of Theorem 9.6 for `ℜ r₁`** (Goldie 1991, proof of Theorem 3.2(i),
pp. 154–155). Under the hypotheses of Theorem 3.2 and (3.7), for an admissible rectangle
contour `𝒞`, the function `f := ℜ r₁`, with `r₁(t) = C₊ − r(t) − g₁ ∗ c(t) 1_{t>0}`, is
measurable, bounded, and satisfies the Tauberian condition (9.25) with `p = 1`:
`f(x) − f(x + y) ≤ A e^{−βx/2}` for `0 ≤ y ≤ e^{−βx/2}`, `x > x₀`, for some `A`, `x₀`. -/
theorem r1_bounded_tauberian {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (hM : Measurable M) (hR : Measurable R) (hM_nonneg : ∀ᵐ ω ∂P, 0 ≤ M ω)
    (h_indep : IndepFun R M P) (κ β : ℝ) (hκ : 0 < κ) (hβ : 0 < β)
    (h_2_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ κ) ∂P = 1)
    (h_3_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ (κ + β)) ∂P < ⊤)
    (h_3_4 : SpreadOut (logLawGivenNonzero P M))
    (h_stone : StoneConditions (tiltedLaw P M κ) β)
    (h_3_7 : IntegrableOn (fun t : ℝ =>
        (P.real {ω | t < R ω} - P.real {ω | t < M ω * R ω}) * t ^ (κ + β - 1)) (Set.Ioi 0))
    (z w : ℂ)
    (h_C : EnclosesZerosInStrip (fun θ => 1 - charTransform (tiltedLaw P M κ) θ) β z w) :
    Measurable (fun t : ℝ => (r1Fun P M R κ z w t).re) ∧
    (∃ B : ℝ, ∀ x : ℝ, |(r1Fun P M R κ z w x).re| ≤ B) ∧
    ∃ A x₀ : ℝ, ∀ x : ℝ, x₀ < x → ∀ y : ℝ, 0 ≤ y → y ≤ Real.exp (-(β * x) / 2) →
      (r1Fun P M R κ z w x).re - (r1Fun P M R κ z w (x + y)).re ≤
        A * Real.exp (-(β * x) / 2) := by sorry

end GoldieRenewal.Rates
