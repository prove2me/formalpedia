-- Prove2me | Theorems.Thm_MeanFieldContest_lemma_3_8
-- name    : MeanFieldContest.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:55:03.137226+00:00
-- url     : https://prove2.me/theorems/34e32091-f389-4a7c-86a9-d33aaab2e164
-- title:
--   Lemma 3.8 — a concave majorant $\varphi$ with $\int(1-g^{-1}\circ\varphi)<1$ gives a better $F^\prime$
-- statement:
--   Let $R$ be a reward function, $\mu<\bar\mu_\infty$ and $F\in\mathcal F'$. Suppose there is an increasing concave function $\varphi\ge\Phi(F)$ on $[0,h(\infty)]$ with $\varphi(1)\le\Phi(F)^{conc}(1)$ and
--   $$\int_0^{h(\infty)}\big(1-g^{-1}\circ\varphi(w)\big)\,dw<1.$$
--   Then there is $F'\in\mathcal F$ with $\Phi(F')^{conc}(1)<\Phi(F)^{conc}(1)$, and consequently $F$ cannot be a mean field equilibrium.
--
--   This is the improvement step of the minimization over $\mathcal F$: slack in the feasibility constraint can be spent to lower the envelope.
--
--   Differences from the source:
--   - encoding: R : [0,1] → ℝ₊ → R : ℝ → ℝ with every condition stated on [0,1]; reason: no object reads R outside [0,1]
--   - encoding: a randomized stopping time τ < ∞ of the absorbed process → a stopping time of a filtration 𝔾 for which W is a Brownian motion, finite a.s., on a probability space Ω : Type, with a.e.-measurable stopping position; reason: a randomized stopping time is a stopping time of a larger filtration; the measurability only excludes the junk value of Measure.map; the law is what is quantified over
--   - encoding: g⁻¹ on [R(1), R(0)] → g⁻¹(z) = 1 ∧ inf{y ∈ [0,1] : g(y) > z} for every real z; reason: the paper’s own extension on p.18; it agrees with p.5 on [R(1), R(0)]
--   - encoding: concave envelope on ℝ₊, with F∘h⁻¹ and ξ^F∘h⁻¹ on [0, h(∞)] → concOn on D = [0, h(∞)] ∩ ℝ (supremum over finite convex combinations), with F∘h⁻¹(h(∞)) := 1 and ξ^F∘h⁻¹(h(∞)) := g(1) when h(∞) < ∞; reason: D is ℝ₊ for µ ≤ 0 and the functions are not defined beyond h(∞) for µ > 0; the values at h(∞) are the limits; for these bounded functions the supremum is the smallest concave majorant at points of D
--   - encoding: ∫₀^{h(∞)} (1 − g⁻¹∘φ) dw → the lintegral over D of ofReal(1 − g⁻¹∘φ); reason: the integrand lies in [0,1]
-- source:
--   Nutz–Zhang, Mean Field Contest with Singularity, arXiv:2103.04219v1, Lemma 3.8, p.13

import Mathlib
import Definitions.Def_TractableComposite_concOn
import Definitions.Def_MeanFieldContest_Model
import Definitions.Def_MeanFieldContest_EnvelopeObjects

open MeasureTheory ProbabilityTheory Set

namespace MeanFieldContest

/-- **Lemma 3.8**, arXiv:2103.04219v1, p.13. Let `F ∈ 𝓕′`. Suppose there exists an increasing concave function
`φ ≥ Φ(F)` on `[0, h(∞)]` satisfying `φ(1) ≤ Φ(F)^conc(1)` and `∫₀^{h(∞)} (1 − g⁻¹ ∘ φ(w)) dw < 1`.
Then there exists `F′ ∈ 𝓕` with `Φ(F′)^conc(1) < Φ(F)^conc(1)`, and consequently `F` cannot be a mean
field equilibrium.

**Formalization Note.** `[0, h(∞)]` is `D = hDomain`. The integrand lies in `[0,1]` for the extended
`g⁻¹`, and the integral is a lower integral over `D`. -/
theorem lemma_3_8 {x₀ μ σ : ℝ} {R : ℝ → ℝ} {F : Measure ℝ}
    (hx₀ : 0 < x₀) (hσ : 0 < σ) (hR : IsRewardFunction R) (hμ : μ < muBarInfty R x₀ σ)
    (hF : F ∈ feasibleLawsPrime x₀ μ σ R) {φ : ℝ → ℝ}
    (hφ_mono : MonotoneOn φ (hDomain x₀ μ σ)) (hφ_conc : ConcaveOn ℝ (hDomain x₀ μ σ) φ)
    (hφ_ge : ∀ w ∈ hDomain x₀ μ σ, Phi x₀ μ σ R F w ≤ φ w)
    (hφ_one : φ 1 ≤ TractableComposite.concOn (hDomain x₀ μ σ) (Phi x₀ μ σ R F) 1)
    (hφ_int : ∫⁻ w in hDomain x₀ μ σ, ENNReal.ofReal (1 - gInv R (φ w)) < 1) :
    (∃ F' ∈ feasibleLaws x₀ μ σ,
      TractableComposite.concOn (hDomain x₀ μ σ) (Phi x₀ μ σ R F') 1 <
        TractableComposite.concOn (hDomain x₀ μ σ) (Phi x₀ μ σ R F) 1) ∧
    ¬ IsMFE x₀ μ σ R F := by sorry

end MeanFieldContest
