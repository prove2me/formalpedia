-- Prove2me | Theorems.Thm_NonconvexSaddle_PSGD_lemma_31
-- name    : NonconvexSaddle.PSGD.lemma_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:16:32.694147+00:00
-- url     : https://prove2.me/theorems/aae726a2-2d4d-4c17-8258-114be04109cd
-- title:
--   Lemma 31 — the terms $q_h+q_{sg}$ of the coupled runs stay small
-- statement:
--   In the setting of Lemma 30 ($f$ satisfying Assumption A, $g$ satisfying Assumption B, $d\ge1$, $\rho,\epsilon>0$, $\sqrt{\rho\epsilon}\le\ell$, $\mathfrak N$ as in Eq. (4), $\eta,r,\mathscr T,\mathscr F,\mathscr S$ as in Eq. (8), the saddle point $x_0$, the unit minimum eigendirection $e_1$ of $\mathcal H=\nabla^2f(x_0)$, the coupled runs of Definition 26, $-\gamma:=\lambda_{\min}(\mathcal H)$ and $\beta$ from Lemma 29 with $a=\eta\gamma$), there is an absolute constant $c_{\max}>0$ such that for every $\iota\ge c_{\max}$,
--   $$\mathbb P\Big(\min\{f(x_{\mathscr T})-f(x_0),\,f(x'_{\mathscr T})-f(x_0)\}\le-\mathscr F,\ \text{or}\ \forall t\le\mathscr T:\ \|q_h(t)+q_{sg}(t)\|\le\frac{\beta(t)\,\eta r}{20\sqrt d}\Big)\ge1-10d\mathscr T^2\log\Big(\frac{\mathscr S\sqrt d}{\eta r}\Big)e^{-\iota}.$$
--
--   Unless one of the coupled runs already escapes, the Hessian-deviation and stochastic-gradient terms stay below a twentieth of the scale of the perturbation term, so the perturbation dominates the difference of the two runs.
--
--   **Formalization Note** $\mathfrak N$ covers both cases of Eq. (4): Assumption C with some $\tilde\ell$, or $\tilde\ell=+\infty$. The constant comes before every other object.
-- source:
--   Jin, Netrapalli, Ge, Kakade, Jordan, On Nonconvex Optimization for Machine Learning: Gradients, Stochasticity, and Saddle Points, arXiv:1902.04811v2, p. 27, Lemma 31

import Mathlib
import Definitions.Def_NonconvexSaddle_PSGD_Setting

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace NonconvexSaddle.PSGD

/-- Lemma 31 (arXiv:1902.04811v2, App. B.3, p. 27), in the setting of Lemmas 25–29: coupling
sequences from the saddle point `x₀`, `η, r, 𝒯, ℱ, 𝒮` as in Eq. (8), `−γ := λ_min(ℋ)` with
`ℋ = ∇²f(x₀)`, and `ι ≥ c_max`. `q_h`, `q_sg` are the terms of Lemma 28 for the runs on `ω` and on
`couple e₁ ω`. -/
theorem lemma_31 :
    ∃ cmax : ℝ, 0 < cmax ∧ ∀ (d : ℕ) (Θ : Type) [MeasurableSpace Θ] (𝒟 : Measure Θ)
      [IsProbabilityMeasure 𝒟] (g : E d → Θ → E d) (f : E d → ℝ) (ℓ ρ σ ε N ι : ℝ)
      (x₀ e₁ : E d),
      1 ≤ d → AssumptionA f ℓ ρ → AssumptionB f g 𝒟 σ → Measurable (Function.uncurry g) →
      0 < ρ → 0 < ε → Real.sqrt (ρ * ε) ≤ ℓ → IsFrakN g 𝒟 ℓ ρ σ ε N → cmax ≤ ι →
      ‖gradient f x₀‖ ≤ ε → lamMin (hess f x₀) ≤ -Real.sqrt (ρ * ε) →
      ‖e₁‖ = 1 → hess f x₀ e₁ = lamMin (hess f x₀) • e₁ →
      let η := etaP ι ℓ N
      let r := rP ι ε N
      let 𝒯 := TcalP ι η ρ ε
      let ℱ := FcalP ι ρ ε
      let 𝒮 := ScalP ι ρ ε
      let γ := -lamMin (hess f x₀)
      ENNReal.ofReal (1 - 10 * d * (𝒯 : ℝ) ^ 2 *
          Real.log (𝒮 * Real.sqrt d / (η * r)) * Real.exp (-ι)) ≤
        noiseLaw (d := d) 𝒟 r {ω |
          min (f (psgd g η x₀ ω 𝒯) - f x₀) (f (psgd g η x₀ (couple e₁ ω) 𝒯) - f x₀) ≤ -ℱ ∨
            ∀ t ≤ 𝒯,
              ‖qh f (hess f x₀) η (psgd g η x₀ ω) (psgd g η x₀ (couple e₁ ω)) t +
                qsg f g (hess f x₀) η ω (psgd g η x₀ ω) (psgd g η x₀ (couple e₁ ω)) t‖ ≤
                betaL (η * γ) t * η * r / (20 * Real.sqrt d)} := by sorry

end NonconvexSaddle.PSGD
