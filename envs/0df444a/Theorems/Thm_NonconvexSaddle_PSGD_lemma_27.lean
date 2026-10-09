-- Prove2me | Theorems.Thm_NonconvexSaddle_PSGD_lemma_27
-- name    : NonconvexSaddle.PSGD.lemma_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:16:17.142478+00:00
-- url     : https://prove2.me/theorems/89edbbba-c0a6-4265-985c-e9e1064169b9
-- title:
--   Lemma 27 — localization of the coupled PSGD runs
-- statement:
--   Let $f$ satisfy Assumption A, let $g$ satisfy Assumption B, let $d\ge1$, $\rho>0$, $\epsilon>0$ and $\sqrt{\rho\epsilon}\le\ell$, let $\mathfrak N$ be as in Eq. (4), and let $\eta,r,\mathscr T,\mathscr F,\mathscr S$ be chosen as in Eq. (8). Let $x_0$ satisfy $\|\nabla f(x_0)\|\le\epsilon$ and $\lambda_{\min}(\nabla^2 f(x_0))\le-\sqrt{\rho\epsilon}$, and let $e_1$ be a unit minimum eigendirection of $\mathcal H=\nabla^2 f(x_0)$. Let $\{x_t\}$ and $\{x'_t\}$ be coupling sequences (Definition 26): PSGD runs from $x_0$ sharing $\theta_\tau$ and the part of $\xi_\tau$ orthogonal to $e_1$, with $e_1^\top\xi'_\tau=-e_1^\top\xi_\tau$. There is an absolute constant $c_0>0$ such that whenever $\iota\ge c_0$,
--   $$\mathbb P\Big(\min\{f(x_{\mathscr T})-f(x_0),\,f(x'_{\mathscr T})-f(x_0)\}\le-\mathscr F,\ \text{or}\ \forall t\le\mathscr T:\ \max\{\|x_t-x_0\|^2,\|x'_t-x_0\|^2\}\le\mathscr S^2\Big)\ge1-16d\mathscr T e^{-\iota}.$$
--
--   Either one of the two coupled runs makes a large decrease, or both stay within distance $\mathscr S$ of the saddle point for $\mathscr T$ steps.
--
--   **Formalization Note** The page states the lemma without a lower bound on $\iota$; its proof applies Lemma 24 with the parameters (8), which needs $\iota$ to exceed an absolute constant, recorded as $c_0\le\iota$. The constant comes before every other object. The integer $\mathscr T$ is $\lceil\iota/(\eta\sqrt{\rho\epsilon})\rceil$.
-- source:
--   Jin, Netrapalli, Ge, Kakade, Jordan, On Nonconvex Optimization for Machine Learning: Gradients, Stochasticity, and Saddle Points, arXiv:1902.04811v2, p. 25, Definition 26 and Lemma 27

import Mathlib
import Definitions.Def_NonconvexSaddle_PSGD_Setting

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace NonconvexSaddle.PSGD

/-- Lemma 27 (Localization; arXiv:1902.04811v2, App. B.3, p. 25), for the coupling sequences of
Definition 26 started at the saddle point `x₀` of Lemma 25, with `η, r, 𝒯, ℱ, 𝒮` as in Eq. (8) and
`ι` at least an absolute constant `c₀`. `x` is the PSGD run on `ω` and `x'` the coupled run on
`couple e₁ ω`, where `e₁` is a unit minimum eigendirection of `ℋ = ∇²f(x₀)`. -/
theorem lemma_27 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (d : ℕ) (Θ : Type) [MeasurableSpace Θ] (𝒟 : Measure Θ)
      [IsProbabilityMeasure 𝒟] (g : E d → Θ → E d) (f : E d → ℝ) (ℓ ρ σ ε N ι : ℝ)
      (x₀ e₁ : E d),
      1 ≤ d → AssumptionA f ℓ ρ → AssumptionB f g 𝒟 σ → Measurable (Function.uncurry g) →
      0 < ρ → 0 < ε → Real.sqrt (ρ * ε) ≤ ℓ → IsFrakN g 𝒟 ℓ ρ σ ε N → c₀ ≤ ι →
      ‖gradient f x₀‖ ≤ ε → lamMin (hess f x₀) ≤ -Real.sqrt (ρ * ε) →
      ‖e₁‖ = 1 → hess f x₀ e₁ = lamMin (hess f x₀) • e₁ →
      let η := etaP ι ℓ N
      let r := rP ι ε N
      let 𝒯 := TcalP ι η ρ ε
      let ℱ := FcalP ι ρ ε
      let 𝒮 := ScalP ι ρ ε
      ENNReal.ofReal (1 - 16 * d * (𝒯 : ℝ) * Real.exp (-ι)) ≤
        noiseLaw (d := d) 𝒟 r {ω |
          min (f (psgd g η x₀ ω 𝒯) - f x₀) (f (psgd g η x₀ (couple e₁ ω) 𝒯) - f x₀) ≤ -ℱ ∨
            ∀ t ≤ 𝒯, max (‖psgd g η x₀ ω t - x₀‖ ^ 2)
              (‖psgd g η x₀ (couple e₁ ω) t - x₀‖ ^ 2) ≤ 𝒮 ^ 2} := by sorry

end NonconvexSaddle.PSGD
