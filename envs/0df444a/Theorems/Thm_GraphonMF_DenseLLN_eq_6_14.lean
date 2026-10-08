-- Prove2me | Theorems.Thm_GraphonMF_DenseLLN_eq_6_14
-- name    : GraphonMF.DenseLLN.eq_6_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:39.958911+00:00
-- url     : https://prove2.me/theorems/10a9f4a4-1239-4649-8ab1-98d1561d58d8
-- title:
--   (6.14), p. 3608 — limsup_{η→0} limsup_n E W_{2,T}(μⁿ, (1/n) Σᵢ δ_{X^{G̃_η}_{i/n}}) = 0
-- statement:
--   Assume Conditions 2.1, 2.2(a) and 3.1 (step graphons $G_n$, weights $\xi^n_{ij}$ as in 3.1(b), and $G_n\to G$ in the cut metric for a graphon $G$), and let $X^n$ solve the $n$-particle system (3.1) for every $n$, with empirical measure $\mu^n=\frac1n\sum_i\delta_{X^n_i}$. For each $\eta\in(0,1)$ let $\tilde G_\eta$ be a continuous graphon with $\|\tilde G_\eta-G\|<\eta$ and let $X^{\tilde G_\eta}$ solve (2.1) for $\tilde G_\eta$. Then
--   $$\limsup_{\eta\to0}\ \limsup_{n\to\infty}\ \mathbb E\,W_{2,T}\Big(\mu^n,\ \frac1n\sum_{i=1}^n\delta_{X^{\tilde G_\eta}_{i/n}}\Big)=0 .$$
--
--   Together with (6.12) and (6.13), this proves (3.3).
--
--   **Formalization Note** Since the quantity is nonnegative, "$\limsup_{\eta\to0}=0$" is stated as convergence to $0$ along $\eta\to0^+$. The expectation is a lower Lebesgue integral of a $[0,\infty]$-valued distance. The family $(\tilde G_\eta,X^{\tilde G_\eta})$ is arbitrary subject to the stated properties, as on the page. Each $\xi^n$ is assumed measurable (needed for the $n$-particle filtration).
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3608, (6.14)

import Mathlib
import Definitions.Def_GraphonMF_DenseLLN_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GraphonMF.DenseLLN
theorem eq_6_14 {Ω : Type*} [MeasurableSpace Ω] {T : ℝ≥0} {d N : ℕ} {P : Measure Ω}
    {μ0 : GraphonMF.Stability.I → Measure (GraphonMF.Stability.State d)} {X0 : GraphonMF.Stability.I → Ω → GraphonMF.Stability.State d} {B : GraphonMF.Stability.I → ℝ≥0 → Ω → GraphonMF.Stability.State d}
    (noise : NoiseSetting P μ0 X0 B) (hT : 0 < T)
    (b : GraphonMF.Stability.State d → GraphonMF.Stability.State d → GraphonMF.Stability.State d) (σ : GraphonMF.Stability.State d → GraphonMF.Stability.State d → Matrix (Fin d) (Fin d) ℝ)
    (ε : ℝ) (h21 : GraphonMF.Stability.Cond21 ε μ0 b σ)
    (J : Fin N → Set GraphonMF.Stability.I) (h22a : Cond22a μ0 J)
    (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (hG : GraphonMF.Stability.IsGraphon G)
    (Gs : ℕ → GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (h31a : ∀ n, 0 < n → GraphonMF.Stability.IsStepGraphon n (Gs n))
    (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ) (hξ : ∀ n, Measurable (ξ n))
    (h31b : Cond31b P X0 B ξ Gs)
    (h31c : Tendsto (fun n => GraphonMF.Stability.cutNorm (fun u v => Gs n u v - G u v)) atTop (𝓝 0))
    (Xn : (n : ℕ) → Fin n → Ω → GraphonMF.Stability.Cd T d)
    (hXn : ∀ n, IsParticleSolution noise b σ n (ξ n) (hξ n) (Xn n))
    (Gt : ℝ → GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (Xt : ℝ → GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d)
    (hGt : ∀ η, 0 < η → η < 1 → GraphonMF.Stability.IsGraphon (Gt η) ∧ Continuous (Function.uncurry (Gt η)) ∧
      GraphonMF.Stability.opNorm (fun u v => Gt η u v - G u v) < η)
    (hXt : ∀ η, 0 < η → η < 1 → IsGraphonSolution noise (Gt η) b σ (Xt η)) :
    Tendsto (fun η => limsup (fun n => ∫⁻ ω, GraphonMF.Stability.W2T (empiricalMeasure (fun i => Xn n i ω))
        (empiricalMeasure (fun i => Xt η (GraphonMF.Stability.lab n i) ω)) ∂P) atTop) (𝓝[>] 0) (𝓝 0) := by sorry
end GraphonMF.DenseLLN
