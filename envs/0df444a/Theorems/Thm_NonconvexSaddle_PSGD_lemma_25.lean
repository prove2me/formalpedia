-- Prove2me | Theorems.Thm_NonconvexSaddle_PSGD_lemma_25
-- name    : NonconvexSaddle.PSGD.lemma_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:16:49.498753+00:00
-- url     : https://prove2.me/theorems/4168c9a6-ebe7-493e-8d4c-8f81b6b4d9aa
-- title:
--   Lemma 25 — perturbed SGD escapes a saddle point within $\mathscr T$ steps
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ ($d\ge1$) satisfy Assumption A with $\rho>0$, let $g$ satisfy Assumption B, let $\epsilon>0$ with $\sqrt{\rho\epsilon}\le\ell$, let $\mathfrak N$ be as in Eq. (4) and let $\eta,r,\mathscr T,\mathscr F,\mathscr S$ be chosen as in Eq. (8). There is an absolute constant $c_{\max}>0$ such that for every $\iota$ with $\iota\ge c_{\max}$ and $\iota>c_{\max}\log(\ell\sqrt{d/(\rho\epsilon)})$, and every starting point $x_0$ with
--   $$\|\nabla f(x_0)\|\le\epsilon\qquad\text{and}\qquad\lambda_{\min}(\nabla^2f(x_0))\le-\sqrt{\rho\epsilon},$$
--   the PSGD run from $x_0$ satisfies
--   $$\mathbb P\big(f(x_{\mathscr T})-f(x_0)\le0.1\mathscr F\big)\ge1-4e^{-\iota}\qquad\text{and}\qquad \mathbb P\big(f(x_{\mathscr T})-f(x_0)\le-\mathscr F\big)\ge\frac13-5d\mathscr T^2\log\Big(\frac{\mathscr S\sqrt d}{\eta r}\Big)e^{-\iota}.$$
--
--   Near a strict saddle point, PSGD never increases the function value by much, and with constant probability it decreases it by $\mathscr F$ within $\mathscr T$ steps. This is the second engine of the proof of Theorem 16.
--
--   **Formalization Note** The page states the lemma at any fixed time $t_0$ at which $x_{t_0}$ is a saddle point; since the algorithm is Markovian, the paper proves the case $t_0=0$, which is the statement here with a deterministic starting point. The proof also takes $\iota$ larger than an absolute constant (p. 28), recorded as $c_{\max}\le\iota$. The constant comes before every other object.
-- source:
--   Jin, Netrapalli, Ge, Kakade, Jordan, On Nonconvex Optimization for Machine Learning: Gradients, Stochasticity, and Saddle Points, arXiv:1902.04811v2, p. 25, Lemma 25 (proof pp. 25–28)

import Mathlib
import Definitions.Def_NonconvexSaddle_PSGD_Setting

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace NonconvexSaddle.PSGD

/-- Lemma 25 (Escaping Saddle Point; arXiv:1902.04811v2, App. B.3, p. 25), in the special case
`t₀ = 0` to which the paper reduces it, with a deterministic start `x₀` satisfying
`‖∇f(x₀)‖ ≤ ε` and `λ_min(∇²f(x₀)) ≤ −√(ρε)`, and `η, r, 𝒯, ℱ, 𝒮` chosen as in Eq. (8). -/
theorem lemma_25 :
    ∃ cmax : ℝ, 0 < cmax ∧ ∀ (d : ℕ) (Θ : Type) [MeasurableSpace Θ] (𝒟 : Measure Θ)
      [IsProbabilityMeasure 𝒟] (g : E d → Θ → E d) (f : E d → ℝ) (ℓ ρ σ ε N ι : ℝ) (x₀ : E d),
      1 ≤ d → AssumptionA f ℓ ρ → AssumptionB f g 𝒟 σ → Measurable (Function.uncurry g) →
      0 < ρ → 0 < ε → Real.sqrt (ρ * ε) ≤ ℓ → IsFrakN g 𝒟 ℓ ρ σ ε N →
      cmax ≤ ι → cmax * Real.log (ℓ * Real.sqrt d / Real.sqrt (ρ * ε)) < ι →
      ‖gradient f x₀‖ ≤ ε → lamMin (hess f x₀) ≤ -Real.sqrt (ρ * ε) →
      let η := etaP ι ℓ N
      let r := rP ι ε N
      let 𝒯 := TcalP ι η ρ ε
      let ℱ := FcalP ι ρ ε
      let 𝒮 := ScalP ι ρ ε
      ENNReal.ofReal (1 - 4 * Real.exp (-ι)) ≤
          noiseLaw (d := d) 𝒟 r {ω | f (psgd g η x₀ ω 𝒯) - f x₀ ≤ 0.1 * ℱ} ∧
        ENNReal.ofReal (1 / 3 - 5 * d * (𝒯 : ℝ) ^ 2 *
            Real.log (𝒮 * Real.sqrt d / (η * r)) * Real.exp (-ι)) ≤
          noiseLaw (d := d) 𝒟 r {ω | f (psgd g η x₀ ω 𝒯) - f x₀ ≤ -ℱ} := by sorry

end NonconvexSaddle.PSGD
