-- Prove2me | Theorems.Thm_MeanFieldContest_lemma_3_7
-- name    : MeanFieldContest.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:55:18.16601+00:00
-- url     : https://prove2.me/theorems/e951a7f3-6d62-4785-8d65-41e252af791f
-- title:
--   Lemma 3.7 — an equilibrium lies in $\mathcal F^\prime$ and $F\circ h^{-1}(\bar w_F)=1$
-- statement:
--   Let $R$ be a reward function and $\mu<\bar\mu_\infty$. If $F$ is a mean field equilibrium, then $F\in\mathcal F'$ and
--   $$\bar w_F=\inf\{w\in[0,h(\infty)]:F\circ h^{-1}(w)=1\}.$$
--   In particular, $F\circ h^{-1}(\bar w_F)=1$.
--
--   So $\Phi(F)$ reaches its top level exactly where $F$ reaches $1$, and strictly beyond the starting point $w=1$.
--
--   Differences from the source:
--   - encoding: R : [0,1] → ℝ₊ → R : ℝ → ℝ with every condition stated on [0,1]; reason: no object reads R outside [0,1]
--   - encoding: a randomized stopping time τ < ∞ of the absorbed process → a stopping time of a filtration 𝔾 for which W is a Brownian motion, finite a.s., on a probability space Ω : Type, with a.e.-measurable stopping position; reason: a randomized stopping time is a stopping time of a larger filtration; the measurability only excludes the junk value of Measure.map; the law is what is quantified over
--   - encoding: concave envelope on ℝ₊, with F∘h⁻¹ and ξ^F∘h⁻¹ on [0, h(∞)] → concOn on D = [0, h(∞)] ∩ ℝ (supremum over finite convex combinations), with F∘h⁻¹(h(∞)) := 1 and ξ^F∘h⁻¹(h(∞)) := g(1) when h(∞) < ∞; reason: D is ℝ₊ for µ ≤ 0 and the functions are not defined beyond h(∞) for µ > 0; the values at h(∞) are the limits; for these bounded functions the supremum is the smallest concave majorant at points of D
--   - encoding: F∘h⁻¹(w̄_F) = 1 → stated for the real value of w̄_F; reason: at w̄_F = h(∞) = +∞ the paper calls it trivial and it has no content
-- source:
--   Nutz–Zhang, Mean Field Contest with Singularity, arXiv:2103.04219v1, Lemma 3.7, p.12; definitions of w̄_F, ȳ, 𝓕′, p.12

import Mathlib
import Definitions.Def_MeanFieldContest_Model
import Definitions.Def_MeanFieldContest_EnvelopeObjects

open MeasureTheory ProbabilityTheory Set

namespace MeanFieldContest

/-- **Lemma 3.7**, arXiv:2103.04219v1, p.12. If `F` is a mean field equilibrium, then `F ∈ 𝓕′` and
`w̄_F = inf{w ∈ [0, h(∞)] : F ∘ h⁻¹(w) = 1}`. In particular, `F ∘ h⁻¹(w̄_F) = 1`.

**Formalization Note.** The infimum is in `EReal`. The last clause is stated at the real value of
`w̄_F`; when `w̄_F = h(∞) = +∞` the paper calls it trivial and it has no content. -/
theorem lemma_3_7 {x₀ μ σ : ℝ} {R : ℝ → ℝ} {F : Measure ℝ}
    (hx₀ : 0 < x₀) (hσ : 0 < σ) (hR : IsRewardFunction R) (hμ : μ < muBarInfty R x₀ σ)
    (hF : IsMFE x₀ μ σ R F) :
    F ∈ feasibleLawsPrime x₀ μ σ R ∧
      wBar x₀ μ σ R F =
        sInf ((fun w : ℝ => (w : EReal)) '' {w | w ∈ hDomain x₀ μ σ ∧ cdfScale x₀ μ σ F w = 1}) ∧
      ∀ w : ℝ, (w : EReal) = wBar x₀ μ σ R F → cdfScale x₀ μ σ F w = 1 := by sorry

end MeanFieldContest
