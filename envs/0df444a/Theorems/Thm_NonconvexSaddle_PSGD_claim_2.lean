-- Prove2me | Theorems.Thm_NonconvexSaddle_PSGD_claim_2
-- name    : NonconvexSaddle.PSGD.claim_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:16:23.89433+00:00
-- url     : https://prove2.me/theorems/b1ff8010-09b1-427f-9256-e524aaaec4c8
-- title:
--   Theorem 16, Claim 2 — at most $T/4$ PSGD iterates are close to saddle points
-- statement:
--   Under the hypotheses of Theorem 16 and Claim 1 (same $\mathfrak N$, $\Delta_f$, parameters (8), $T$ and $Q$), let also $\mathscr S$ be as in Eq. (8). There is an absolute constant $\mu_0>0$ such that whenever $\iota\ge\mu_0(1+\log Q)$, with probability at least
--   $$1-10\,d\,\mathscr T^2T^2\log\Big(\frac{\mathscr S\sqrt d}{\eta r}\Big)e^{-\iota}$$
--   at most $T/4$ of the iterates $x_0,\dots,x_{T-1}$ are close to saddle points:
--   $$4\cdot\#\{t<T:\ \|\nabla f(x_t)\|\le\epsilon\ \text{and}\ \lambda_{\min}(\nabla^2f(x_t))\le-\sqrt{\rho\epsilon}\}\le T.$$
--
--   Together with Claim 1 this leaves at least $T/2$ of the iterates $\epsilon$-second-order stationary.
--
--   **Formalization Note** The calibration of $\iota$ is the one of Theorem 16. The probability is the one the proof establishes (p. 29).
-- source:
--   Jin, Netrapalli, Ge, Kakade, Jordan, On Nonconvex Optimization for Machine Learning: Gradients, Stochasticity, and Saddle Points, arXiv:1902.04811v2, pp. 28–29, proof of Theorem 16, Claim 2

import Mathlib
import Definitions.Def_NonconvexSaddle_PSGD_Setting

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace NonconvexSaddle.PSGD

/-- Claim 2 of the proof of Theorem 16 (arXiv:1902.04811v2, App. B.4, pp. 28–29): under the
hypotheses of Theorem 16, with probability at least `1 − 10d𝒯²T² · log(𝒮√d/(ηr)) e^{−ι}` at most
`T/4` of the iterates `x₀, …, x_{T−1}` are close to saddle points, `‖∇f(x_t)‖ ≤ ε` and
`λ_min(∇²f(x_t)) ≤ −√(ρε)`. -/
theorem claim_2 :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ (d : ℕ) (Θ : Type) [MeasurableSpace Θ] (𝒟 : Measure Θ)
      [IsProbabilityMeasure 𝒟] (g : E d → Θ → E d) (f : E d → ℝ) (ℓ ρ σ ε δ N ι : ℝ)
      (x₀ : E d),
      1 ≤ d → AssumptionA f ℓ ρ → AssumptionB f g 𝒟 σ → Measurable (Function.uncurry g) →
      BddBelow (Set.range f) → 0 < ρ → 0 < ε → 0 < δ → δ < 1 → Real.sqrt (ρ * ε) ≤ ℓ →
      IsFrakN g 𝒟 ℓ ρ σ ε N →
      μ₀ * (1 + Real.log (logArgQ d ℓ ρ ε δ N (f x₀ - fstar f))) ≤ ι →
      let η := etaP ι ℓ N
      let r := rP ι ε N
      let 𝒯 := TcalP ι η ρ ε
      let ℱ := FcalP ι ρ ε
      let 𝒮 := ScalP ι ρ ε
      let T := iterT (f x₀ - fstar f) 𝒯 ℱ η ε
      ENNReal.ofReal (1 - 10 * d * (𝒯 : ℝ) ^ 2 * (T : ℝ) ^ 2 *
          Real.log (𝒮 * Real.sqrt d / (η * r)) * Real.exp (-ι)) ≤
        noiseLaw (d := d) 𝒟 r {ω | 4 * (((Finset.range T).filter
            (fun t => ‖gradient f (psgd g η x₀ ω t)‖ ≤ ε ∧
              lamMin (hess f (psgd g η x₀ ω t)) ≤ -Real.sqrt (ρ * ε))).card : ℝ) ≤
            (T : ℝ)} := by sorry

end NonconvexSaddle.PSGD
