-- Prove2me | Theorems.Thm_KallMayerSLP_RiskMeasures_proposition_5_2
-- name    : KallMayerSLP.RiskMeasures.proposition_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:40:59.599991+00:00
-- url     : https://prove2.me/theorems/7dd5d6a0-ba6c-4d4c-82d5-55571ae424b9
-- title:
--   Proposition 5.2 — the absolute-deviation evaluation function $A(x)=\mathbb E|\eta^\top x-\xi|$ is convex
-- statement:
--   Let $(\eta,\xi)$ be an $(n+1)$-dimensional random vector on a probability space $(\Omega,\mathcal F,P)$ whose expected value exists. Then the evaluation function
--   $$
--   A(x):=\mathbb E\big[\,|\eta^\top x-\xi|\,\big],\qquad x\in\mathbb R^n,
--   $$
--   is convex on $\mathbb R^n$.
--
--   $A(x)=\rho_A(\eta^\top x-\xi)$ measures the absolute deviation between $\eta^\top x$ and $\xi$; its convexity makes the models (5.16) and (5.17) convex programs.
--
--   **Formalization Note** "The expected value exists" is integrability of every component of $\eta$ and of $\xi$.
--
--   Differences from the source:
--   - encoding: A(x) := 𝔼[|ηᵀx − ξ|] → rhoA P (fun ω => η ω ⬝ᵥ x − ξ ω), with rhoA P ϑ = ∫ |ϑ| ∂P; reason: the same function
--   - encoding: x ∈ ℝⁿ, ηᵀx → x : Fin n → ℝ, η ω ⬝ᵥ x; reason: Lean convention; same instances
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §5.2, (5.14)–(5.15), p.169 (PDF 179), and Proposition 5.2, p.170 (PDF 180)

import Mathlib
import Definitions.Def_KallMayerSLP_RiskMeasures_rhoA

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Proposition 5.2** (convexity of the absolute-deviation evaluation function).
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §5.2, (5.14)–(5.15) and Prop. 5.2, pp.169–170 (PDF 179–180), with the standing assumption
of §5 (p.166, PDF 176) that the expected value of `(ηᵀ, ξ)` exists. Then
`A(x) := 𝔼[|ηᵀx − ξ|]` is a convex function of `x ∈ ℝⁿ`.

**Formalization Note.** `A(x) = ρ_A(ηᵀx − ξ)` with `ρ_A(ϑ) = 𝔼|ϑ|`. Vectors are `Fin n → ℝ`,
`ηᵀx` is `η ω ⬝ᵥ x`; "the expected value exists" is integrability of each component of `η` and of
`ξ`. -/
theorem proposition_5_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (η : Ω → Fin n → ℝ) (ξ : Ω → ℝ)
    (hη : ∀ i, Integrable (fun ω => η ω i) P) (hξ : Integrable ξ P) :
    ConvexOn ℝ Set.univ (fun x : Fin n → ℝ => rhoA P (fun ω => η ω ⬝ᵥ x - ξ ω)) := by sorry

end KallMayerSLP.RiskMeasures
