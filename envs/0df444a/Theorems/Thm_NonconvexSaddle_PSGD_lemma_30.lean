-- Prove2me | Theorems.Thm_NonconvexSaddle_PSGD_lemma_30
-- name    : NonconvexSaddle.PSGD.lemma_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:16:01.502985+00:00
-- url     : https://prove2.me/theorems/4e8983c1-4144-4329-9c55-0a7b7a1a155e
-- title:
--   Lemma 30 — the perturbation term $q_p(t)$ of the coupled runs: upper and anti-concentration bounds
-- statement:
--   In the setting of Lemma 27 ($f$ satisfying Assumption A, $g$ satisfying Assumption B, $d\ge1$, $\rho,\epsilon>0$, $\sqrt{\rho\epsilon}\le\ell$, $\mathfrak N$ as in Eq. (4), $\eta,r,\mathscr T$ as in Eq. (8), $x_0$ with $\|\nabla f(x_0)\|\le\epsilon$ and $\lambda_{\min}(\nabla^2f(x_0))\le-\sqrt{\rho\epsilon}$, $e_1$ a unit minimum eigendirection of $\mathcal H=\nabla^2 f(x_0)$, coupled runs as in Definition 26), let $-\gamma:=\lambda_{\min}(\mathcal H)$, let $\beta$ be as in Lemma 29 with $a=\eta\gamma$, and let $\iota\ge1$. There is an absolute constant $c>0$ such that for every $t>0$
--   $$\mathbb P\Big(\|q_p(t)\|\le c\,\beta(t)\frac{\eta r}{\sqrt d}\sqrt\iota\Big)\ge1-2e^{-\iota},$$
--   and
--   $$\mathbb P\Big(\|q_p(\mathscr T)\|\ge\frac{\beta(\mathscr T)\,\eta r}{10\sqrt d}\Big)\ge\frac23.$$
--
--   The perturbation term is never much larger than its scale $\beta(t)\eta r/\sqrt d$, and at the escape time $\mathscr T$ it is at least a constant fraction of that scale with constant probability.
--
--   **Formalization Note** The lemma sits in the setting of Lemma 25 (§B.3, where $\iota$ exceeds an absolute constant); $\iota\ge1$ is what the second bound needs, since it gives $\mathscr T\ge\ln 2/(\eta\gamma)$ in Lemma 29. The constant $c$ comes before every other object.
-- source:
--   Jin, Netrapalli, Ge, Kakade, Jordan, On Nonconvex Optimization for Machine Learning: Gradients, Stochasticity, and Saddle Points, arXiv:1902.04811v2, p. 26, Lemma 30

import Mathlib
import Definitions.Def_NonconvexSaddle_PSGD_Setting

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace NonconvexSaddle.PSGD

/-- Lemma 30 (arXiv:1902.04811v2, App. B.3, p. 26), in the setting of Lemmas 25–29: coupling
sequences from the saddle point `x₀`, `η, r, 𝒯` as in Eq. (8), `−γ := λ_min(ℋ)` with
`ℋ = ∇²f(x₀)`, and `ι ≥ 1`. `q_p` is the perturbation term of Lemma 28 for the runs on `ω` and on
`couple e₁ ω`. -/
theorem lemma_30 :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (Θ : Type) [MeasurableSpace Θ] (𝒟 : Measure Θ)
      [IsProbabilityMeasure 𝒟] (g : E d → Θ → E d) (f : E d → ℝ) (ℓ ρ σ ε N ι : ℝ)
      (x₀ e₁ : E d),
      1 ≤ d → AssumptionA f ℓ ρ → AssumptionB f g 𝒟 σ → Measurable (Function.uncurry g) →
      0 < ρ → 0 < ε → Real.sqrt (ρ * ε) ≤ ℓ → IsFrakN g 𝒟 ℓ ρ σ ε N → 1 ≤ ι →
      ‖gradient f x₀‖ ≤ ε → lamMin (hess f x₀) ≤ -Real.sqrt (ρ * ε) →
      ‖e₁‖ = 1 → hess f x₀ e₁ = lamMin (hess f x₀) • e₁ →
      let η := etaP ι ℓ N
      let r := rP ι ε N
      let 𝒯 := TcalP ι η ρ ε
      let γ := -lamMin (hess f x₀)
      (∀ t : ℕ, 0 < t →
        ENNReal.ofReal (1 - 2 * Real.exp (-ι)) ≤
          noiseLaw (d := d) 𝒟 r {ω | ‖qp (hess f x₀) η ω (couple e₁ ω) t‖ ≤
            c * betaL (η * γ) t * η * r / Real.sqrt d * Real.sqrt ι}) ∧
        ENNReal.ofReal (2 / 3) ≤
          noiseLaw (d := d) 𝒟 r {ω | betaL (η * γ) 𝒯 * η * r / (10 * Real.sqrt d) ≤
            ‖qp (hess f x₀) η ω (couple e₁ ω) 𝒯‖} := by sorry

end NonconvexSaddle.PSGD
