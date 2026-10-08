-- Prove2me | Theorems.Thm_GenEmpLik_Consistency_example_5
-- name    : GenEmpLik.Consistency.example_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:14:36.191017+00:00
-- url     : https://prove2.me/theorems/81d47cad-a774-4d73-930c-a168ef61562d
-- title:
--   Example 5 — a pointwise compact class with integrable envelope is Glivenko–Cantelli
-- statement:
--   Let $\xi_1,\xi_2,\dots$ be i.i.d. random elements of $\Xi$ with law $P_0$. Let $\mathcal X\subset\mathbb R^d$ be compact, let $\ell(x;\cdot)$ be measurable for each $x\in\mathcal X$, and let $x\mapsto\ell(x;\xi)$ be continuous on $\mathcal X$ for $P_0$-almost all $\xi\in\Xi$. If there is a measurable envelope $Z:\Xi\to\mathbb R_+$ with
--
--   $$
--   |\ell(x;\xi)|\le Z(\xi)\quad\text{for all }x\in\mathcal X,\ \xi\in\Xi,\qquad E_{P_0}[Z]<\infty,
--   $$
--
--   then $\mathcal H=\{\ell(x;\cdot):x\in\mathcal X\}$ is Glivenko–Cantelli.
--
--   This is the standard sufficient condition (van der Vaart, *Asymptotic Statistics*, Example 19.8) by which the Glivenko–Cantelli hypothesis of Theorem 7 is verified for continuous losses on a compact decision set; Corollary 1 uses it in exactly this way.
--
--   **Formalization Note** Samples are 0-based and $P_0$ is the law of $\xi_0$; "Glivenko–Cantelli" is the definition of this mission (integrable class, supremum in $[0,\infty]$, convergence `∀ᵐ`). The continuity is assumed for $P_0$-almost every $\xi$, as printed.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 16, Example 5 (quoting van der Vaart 1998, Example 19.8)

import Mathlib
import Definitions.Def_GenEmpLik_Consistency_IsGlivenkoCantelli

open MeasureTheory ProbabilityTheory Filter Topology

namespace GenEmpLik.Consistency

/-- Example 5 (arXiv:1610.03425v3, p. 16; van der Vaart 1998, Example 19.8). Let `ξ₀, ξ₁, …`
be i.i.d. with law `P₀`, let `X` be compact, let `ℓ(·; ξ)` be continuous on `X` for
`P₀`-almost every `ξ`, and let `ℓ(x; ·)` be measurable for each `x ∈ X`. If there is a measurable envelope
`Z : Ξ → ℝ₊` with `|ℓ(x; ξ)| ≤ Z(ξ)` for all `x ∈ X`, `ξ ∈ Ξ` and `E_{P₀}[Z] < ∞`, then
`{ℓ(x; ·) : x ∈ X}` is Glivenko–Cantelli. -/
theorem example_5 {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {d : ℕ}
    (ξ : ℕ → Ω → Ξ) (hξm : ∀ i, Measurable (ξ i)) (hξind : iIndepFun ξ μ)
    (hξid : ∀ i, IdentDistrib (ξ i) (ξ 0) μ μ)
    (X : Set (EuclideanSpace ℝ (Fin d))) (hX : IsCompact X)
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (hℓm : ∀ x ∈ X, Measurable (ℓ x))
    (hcont : ∀ᵐ s ∂(μ.map (ξ 0)), ContinuousOn (fun x => ℓ x s) X)
    (Z : Ξ → ℝ) (hZm : Measurable Z) (hZ0 : ∀ s, 0 ≤ Z s)
    (hZ : ∀ x ∈ X, ∀ s, |ℓ x s| ≤ Z s) (hZint : Integrable Z (μ.map (ξ 0))) :
    IsGlivenkoCantelli μ ξ ((fun x => ℓ x) '' X) := by sorry

end GenEmpLik.Consistency
