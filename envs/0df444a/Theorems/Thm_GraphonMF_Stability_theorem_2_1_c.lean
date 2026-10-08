-- Prove2me | Theorems.Thm_GraphonMF_Stability_theorem_2_1_c
-- name    : GraphonMF.Stability.theorem_2_1_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:27:26.469785+00:00
-- url     : https://prove2.me/theorems/d16e143f-1778-41c7-8f1d-cb13fa268f5c
-- title:
--   Theorem 2.1(c) — stability under cut-metric convergence
-- statement:
--   Let $G_n$ and $G$ be graphons, with the same initial-law family, coefficients, initial random variables, and Brownian motions satisfying Condition 2.1. Write $\mu^{G_n}_u$ and $\mu^G_u$ for the path laws of their graphon particle systems. If $G_n\to G$ in cut metric, then
--
--   $$\int_I[W_{2,T}(\mu^{G_n}_u,\mu^G_u)]^2\,du\longrightarrow0.$$
--
--   The result says the family of solution laws depends continuously on the graphon in an integrated Wasserstein metric. It supports the dense and sparse particle limits later in the paper.
--
--   **Formalization Note** Every graphon is measurable, symmetric, and $[0,1]$-valued. Solutions use one common probability space and the solution class $\mathcal M$. The statement also asserts measurability of each Wasserstein integrand, corresponding to Remark 5.1 and the paper's assertion that the displayed integral is well defined. Nonnegative integrals take values in $[0,\infty]$.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3593, Theorem 2.1(c); p. 3601, Remark 5.1

import Mathlib
import Definitions.Def_GraphonMF_Stability_Setting

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace GraphonMF.Stability

/-- Theorem 2.1(c), p. 3593: graphon convergence in cut metric gives L²-Wasserstein stability. -/
theorem theorem_2_1_c {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (T : ℝ≥0)
    (hT : 0 < T) (P : Measure Ω) (μ0 : I → Measure (State d))
    (X0 : I → Ω → State d) (B : I → ℝ≥0 → Ω → State d)
    (noise : NoiseSetting P μ0 X0 B)
    (b : State d → State d → State d)
    (σ : State d → State d → Matrix (Fin d) (Fin d) ℝ)
    (ε : ℝ) (hc : Cond21 ε μ0 b σ)
    (G : I → I → ℝ) (Gs : ℕ → I → I → ℝ)
    (hG : IsGraphon G) (hGs : ∀ n, IsGraphon (Gs n))
    (X : I → Ω → Cd T d) (Xs : ℕ → I → Ω → Cd T d)
    (hX : IsGraphonSolution P μ0 X0 B noise G b σ X)
    (hXs : ∀ n, IsGraphonSolution P μ0 X0 B noise (Gs n) b σ (Xs n))
    (hcut : Tendsto (fun n => cutNorm (fun u v => Gs n u v - G u v)) atTop (𝓝 0)) :
    (∀ n, Measurable (fun u => W2T (law P (Xs n) u) (law P X u))) ∧
      Tendsto (fun n => ∫⁻ u, W2T (law P (Xs n) u) (law P X u) ^ (2 : ℝ))
        atTop (𝓝 0) := by sorry

end GraphonMF.Stability
