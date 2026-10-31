-- Prove2me | Theorems.Thm_KallMayerSLP_RiskMeasures_proposition_5_1
-- name    : KallMayerSLP.RiskMeasures.proposition_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:41:14.813378+00:00
-- url     : https://prove2.me/theorems/883e2dfd-5e1d-4e70-9149-8a9eeb704c45
-- title:
--   Proposition 5.1 — the quadratic-deviation evaluation function $Q(x)=\sqrt{\mathbb E[(\eta^\top x-\xi)^2]}$ is convex
-- statement:
--   Let $(\eta,\xi)$ be an $(n+1)$-dimensional random vector on a probability space $(\Omega,\mathcal F,P)$, with $\eta$ an $n$-dimensional random vector and $\xi$ a random variable, and assume that the second moments of $(\eta^\top,\xi)$ exist. Then the evaluation function
--   $$
--   Q(x):=\sqrt{\mathbb E\big[(\eta^\top x-\xi)^2\big]},\qquad x\in\mathbb R^n,
--   $$
--   is convex on $\mathbb R^n$.
--
--   $Q(x)=\rho_Q(\eta^\top x-\xi)$ is the quadratic deviation between the random variables $\eta^\top x$ and $\xi$; its convexity makes the quadratic-deviation SLP models of §5.1 convex programs.
--
--   **Formalization Note** "Second moments exist" is square integrability of every component of $\eta$ and of $\xi$.
--
--   Differences from the source:
--   - generalization: the second moments of (ηᵀ, ξ) exist and the covariance matrix of (ηᵀ, ξ) is positive definite → second moments exist (MemLp 2 for each component of η and for ξ); no non-degeneracy hypothesis; reason: the book's proof does not use non-degeneracy; dropping a hypothesis gives a statement that specializes to the book's
--   - encoding: Q(x) := √(𝔼[(ηᵀx − ξ)²]) → rhoQ P (fun ω => η ω ⬝ᵥ x − ξ ω), with rhoQ P ϑ = √(∫ ϑ² ∂P); reason: the same function
--   - encoding: x ∈ ℝⁿ, ηᵀx → x : Fin n → ℝ, η ω ⬝ᵥ x; reason: Lean convention; same instances
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §5.1, (5.1) and Proposition 5.1, p.167 (PDF 177); standing assumptions of §5, p.166 (PDF 176)

import Mathlib
import Definitions.Def_KallMayerSLP_RiskMeasures_rhoQ

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Proposition 5.1** (convexity of the quadratic-deviation evaluation function).
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §5.1, (5.1) and Prop. 5.1, p.167 (PDF 177), with the standing assumptions of §5
(p.166, PDF 176): `(η, ξ)` is an `(n+1)`-dimensional random vector on `(Ω, 𝓕, P)` whose second
moments exist. Then
`Q(x) := √(𝔼[(ηᵀx − ξ)²])` is a convex function of `x ∈ ℝⁿ`.

**Formalization Note.** `Q(x) = ρ_Q(ηᵀx − ξ)` with `ρ_Q(ϑ) = √𝔼[ϑ²]`. Vectors are `Fin n → ℝ`,
`ηᵀx` is `η ω ⬝ᵥ x`. "Second moments exist" is `MemLp · 2 P` for each component of `η` and for
`ξ`. The book also assumes the covariance matrix of `(ηᵀ, ξ)` positive definite; that hypothesis
is dropped (its proof does not use it), which makes the statement more general. -/
theorem proposition_5_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (η : Ω → Fin n → ℝ) (ξ : Ω → ℝ)
    (hη : ∀ i, MemLp (fun ω => η ω i) 2 P) (hξ : MemLp ξ 2 P) :
    ConvexOn ℝ Set.univ (fun x : Fin n → ℝ => rhoQ P (fun ω => η ω ⬝ᵥ x - ξ ω)) := by sorry

end KallMayerSLP.RiskMeasures
