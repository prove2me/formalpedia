-- Prove2me | Theorems.Thm_NonconvexSaddle_PSGD_claim_1
-- name    : NonconvexSaddle.PSGD.claim_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:16:37.119178+00:00
-- url     : https://prove2.me/theorems/d9533753-a1c6-4900-a3fe-53591a1eb0b4
-- title:
--   Theorem 16, Claim 1 — at most $T/4$ PSGD iterates have large gradient
-- statement:
--   Assume the hypotheses of Theorem 16: $f:\mathbb R^d\to\mathbb R$ ($d\ge1$) satisfies Assumption A with $\rho>0$ and is bounded below, $g$ satisfies Assumption B, $\epsilon>0$, $0<\delta<1$, $\sqrt{\rho\epsilon}\le\ell$, $\mathfrak N$ is as in Eq. (4), $\Delta_f=f(x_0)-f^\star$, $\eta,r,\mathscr T,\mathscr F$ are as in Eq. (8), and
--   $$T=\Big\lceil100\max\Big\{\frac{\Delta_f\mathscr T}{\mathscr F},\frac{\Delta_f}{\eta\epsilon^2}\Big\}\Big\rceil.$$
--   There is an absolute constant $\mu_0>0$ such that whenever $\iota\ge\mu_0(1+\log Q)$ with $Q=d\,\mathfrak N\max\{1,\ell\Delta_f/\epsilon^2\}\,(\ell/\sqrt{\rho\epsilon})/\delta$, with probability at least $1-4e^{-\iota}$ at most $T/4$ of the iterates $x_0,\dots,x_{T-1}$ have large gradient:
--   $$4\cdot\#\{t<T:\ \|\nabla f(x_t)\|\ge\epsilon\}\le T.$$
--
--   This is the first of the two claims whose conjunction proves Theorem 16.
--
--   **Formalization Note** The calibration of $\iota$ is the one of Theorem 16 (see there). The probability $1-4e^{-\iota}$ is the one the proof establishes (p. 29).
-- source:
--   Jin, Netrapalli, Ge, Kakade, Jordan, On Nonconvex Optimization for Machine Learning: Gradients, Stochasticity, and Saddle Points, arXiv:1902.04811v2, pp. 28–29, proof of Theorem 16, Claim 1

import Mathlib
import Definitions.Def_NonconvexSaddle_PSGD_Setting

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace NonconvexSaddle.PSGD

/-- Claim 1 of the proof of Theorem 16 (arXiv:1902.04811v2, App. B.4, pp. 28–29): under the
hypotheses of Theorem 16, with probability at least `1 − 4e^{−ι}` at most `T/4` of the iterates
`x₀, …, x_{T−1}` have large gradient, `‖∇f(x_t)‖ ≥ ε`. -/
theorem claim_1 :
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
      let T := iterT (f x₀ - fstar f) 𝒯 ℱ η ε
      ENNReal.ofReal (1 - 4 * Real.exp (-ι)) ≤
        noiseLaw (d := d) 𝒟 r {ω | 4 * (((Finset.range T).filter
            (fun t => ε ≤ ‖gradient f (psgd g η x₀ ω t)‖)).card : ℝ) ≤ (T : ℝ)} := by sorry

end NonconvexSaddle.PSGD
