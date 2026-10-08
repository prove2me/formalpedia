-- Prove2me | Theorems.Thm_NonlinSSD_Optimality_theorem_1_subgradient
-- name    : NonlinSSD.Optimality.theorem_1_subgradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:00:41.659254+00:00
-- url     : https://prove2.me/theorems/5177c84f-dff6-4531-bcad-3f164ac1bea5
-- title:
--   Theorem 1 — subgradient characterization of an expected concave optimum
-- statement:
--   Let $\varphi:\mathcal Z\to\mathcal L^1(\Omega;\mathbb R^n)$ be continuous, with almost every realization concave in the componentwise order and continuous on the whole decision space. Let $f:\mathbb R^n\to\mathbb R$ be concave, nondecreasing in the componentwise order, and have uniformly bounded concave superdifferentials. For a convex $Z\subseteq\mathcal Z$ and $\hat z\in Z$, the point $\hat z$ maximizes $\mathbb E f(\varphi(z))$ on $Z$ if and only if there is $\theta\in\mathcal L^\infty(\Omega;\mathbb R^n)$ such that $\theta(\omega)\in\partial f(\varphi(\hat z)(\omega))$ almost surely and
--   $$\mathbb E[\theta\cdot\varphi(z)]\le\mathbb E[\theta\cdot\varphi(\hat z)]\qquad(z\in Z).$$
--
--   This characterization turns the utility maximization appearing in the proof of Theorem 2 into a linear functional optimality condition.
--
--   **Formalization Note** The paper's $\partial f$ is the concave superdifferential, defined by an upper affine support inequality. Its uniform norm bound is a hypothesis. The almost sure statement places the null set outside the quantifier over decisions. The stated hypotheses make both displayed expectations integrable.
-- source:
--   Dentcheva, Ruszczyński, Optimality and duality theory for stochastic optimization problems with nonlinear dominance constraints, author manuscript (rev. April 2003; Math. Program. 2004, DOI 10.1007/s10107-003-0453-z), p. 5, Theorem 1

import Mathlib
import Definitions.Def_NonlinSSD_Optimality_Basic

namespace NonlinSSD.Optimality

open MeasureTheory Filter

/-- Theorem 1, p. 5: an optimizer of expected concave utility is characterized by
an essentially bounded measurable selection of the concave superdifferential. -/
theorem theorem_1_subgradient
    {Ω 𝒵 : Type*} [MeasurableSpace Ω]
    [AddCommGroup 𝒵] [Module ℝ 𝒵] [TopologicalSpace 𝒵]
    [IsTopologicalAddGroup 𝒵] [ContinuousSMul ℝ 𝒵]
    [LocallyConvexSpace ℝ 𝒵] [T2Space 𝒵]
    [TopologicalSpace.SeparableSpace 𝒵]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (φ : 𝒵 → Ω → Fin n → ℝ)
    (hφ_int : ∀ z, Integrable (φ z) P)
    (hφ_cont : ∀ z₀, Tendsto
      (fun z => ∫ ω, ‖φ z ω - φ z₀ ω‖ ∂P) (nhds z₀) (nhds 0))
    (hφ_sample : ∀ᵐ ω ∂P,
      ConcaveOn ℝ Set.univ (fun z => φ z ω) ∧
      Continuous (fun z => φ z ω))
    (f : (Fin n → ℝ) → ℝ)
    (hf_concave : ConcaveOn ℝ Set.univ f)
    (hf_monotone : Monotone f)
    (hf_bound : ∃ c : ℝ, 0 ≤ c ∧
      ∀ y (θ : Fin n → ℝ), θ ∈ superdiff f y → ‖θ‖ ≤ c)
    (Z : Set 𝒵) (hZ : Convex ℝ Z) (zhat : 𝒵) (hzhat : zhat ∈ Z) :
    (∀ z ∈ Z,
      (∫ ω, f (φ z ω) ∂P) ≤ ∫ ω, f (φ zhat ω) ∂P) ↔
    ∃ θ : Ω → Fin n → ℝ,
      MemLp θ ⊤ P ∧
      (∀ᵐ ω ∂P, θ ω ∈ superdiff f (φ zhat ω)) ∧
      ∀ z ∈ Z,
        (∫ ω, ∑ i : Fin n, θ ω i * φ z ω i ∂P) ≤
          ∫ ω, ∑ i : Fin n, θ ω i * φ zhat ω i ∂P := by sorry

end NonlinSSD.Optimality
