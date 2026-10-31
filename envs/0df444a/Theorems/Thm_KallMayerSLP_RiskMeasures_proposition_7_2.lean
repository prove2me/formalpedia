-- Prove2me | Theorems.Thm_KallMayerSLP_RiskMeasures_proposition_7_2
-- name    : KallMayerSLP.RiskMeasures.proposition_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:41:04.579134+00:00
-- url     : https://prove2.me/theorems/80e31fb5-f1a7-49c4-95a1-35d6ad884470
-- title:
--   Proposition 7.2 — convexity, subadditivity and positive homogeneity of $\rho$ pass to $V(x)=\rho(\eta^\top x-\xi)$
-- statement:
--   Let $\Upsilon$ be a linear space of real random variables on $\Omega$ and $\rho:\Upsilon\to\mathbb R$. Let $\eta$ be an $n$-dimensional random vector and $\xi$ a random variable such that $\eta^\top x-\xi\in\Upsilon$ for every $x\in\mathbb R^n$, and put
--   $$
--   V(x):=\rho(\eta^\top x-\xi),\qquad x\in\mathbb R^n .
--   $$
--   Then:
--
--   1. if $\rho$ is convex on $\Upsilon$, then $V$ is convex on $\mathbb R^n$;
--   2. if $\xi\equiv0$ and $\rho$ is subadditive, then $V$ is subadditive;
--   3. if $\xi\equiv0$ and $\rho$ is positive homogeneous, then $V$ is positive homogeneous.
--
--   The properties of $V$ hold for every probability distribution of the data, so a convex risk measure always yields a convex stochastic programming model.
--
--   **Formalization Note** $\Upsilon$ is a submodule of the functions $\Omega\to\mathbb R$; $\rho$ is given on all functions and only its restriction to $\Upsilon$ is assumed convex, subadditive or positively homogeneous. No probability measure is needed.
--
--   Differences from the source:
--   - encoding: ρ : Υ → ℝ → ρ : (Ω → ℝ) → ℝ with hypotheses on its restriction to the submodule Υ; reason: every function on Υ extends to all functions, and V only evaluates ρ on Υ; same instances
--   - encoding: ξ ≡ 0 → ξ = 0 as a function; reason: the book's identity of random variables
--   - encoding: x ∈ ℝⁿ, ηᵀx → x : Fin n → ℝ, η ω ⬝ᵥ x; reason: Lean convention; same instances
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §7, Proposition 7.2, p.182 (PDF 192)

import Mathlib
import Definitions.Def_KallMayerSLP_RiskMeasures_IsPosHomogeneous
import Definitions.Def_KallMayerSLP_RiskMeasures_IsSubadditive

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Proposition 7.2** (properties of `ρ` pass to the evaluation function `V`).
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §7, Prop. 7.2, p.182 (PDF 192). Let `Υ` be a linear space of random variables and
`ρ : Υ → ℝ` a real-valued function on `Υ`. Assume that `ηᵀx − ξ ∈ Υ` for all `x` and let
`V(x) := ρ(ηᵀx − ξ)`. Then
a) if `ρ` is convex then `V` is convex;
b) if `ξ ≡ 0` and `ρ` is subadditive then `V` is subadditive;
c) if `ξ ≡ 0` and `ρ` is positive homogeneous then `V` is positive homogeneous.

**Formalization Note.** `Υ` is a submodule of the functions `Ω → ℝ` and `ρ` a function on
`Ω → ℝ` of which only the restriction to `Υ` is constrained; convexity, subadditivity and positive
homogeneity of `ρ` are those of this restriction (a function on the linear space `Υ`).
`x ∈ ℝⁿ` is `Fin n → ℝ`, `ηᵀx` is `η ω ⬝ᵥ x`; `ξ ≡ 0` is `ξ = 0` as a function. No measure
enters. -/
theorem proposition_7_2 {Ω : Type*} (Υ : Submodule ℝ (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ)
    {n : ℕ} (η : Ω → Fin n → ℝ) (ξ : Ω → ℝ)
    (hΥ : ∀ x : Fin n → ℝ, (fun ω => η ω ⬝ᵥ x - ξ ω) ∈ Υ) :
    (ConvexOn ℝ Set.univ (fun ϑ : Υ => ρ ϑ) →
      ConvexOn ℝ Set.univ (fun x : Fin n → ℝ => ρ (fun ω => η ω ⬝ᵥ x - ξ ω))) ∧
    (ξ = 0 → IsSubadditive (fun ϑ : Υ => ρ ϑ) →
      IsSubadditive (fun x : Fin n → ℝ => ρ (fun ω => η ω ⬝ᵥ x - ξ ω))) ∧
    (ξ = 0 → IsPosHomogeneous (fun ϑ : Υ => ρ ϑ) →
      IsPosHomogeneous (fun x : Fin n → ℝ => ρ (fun ω => η ω ⬝ᵥ x - ξ ω))) := by sorry

end KallMayerSLP.RiskMeasures
