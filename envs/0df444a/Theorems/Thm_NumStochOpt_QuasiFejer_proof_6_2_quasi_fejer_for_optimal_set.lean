-- Prove2me | Theorems.Thm_NumStochOpt_QuasiFejer_proof_6_2_quasi_fejer_for_optimal_set
-- name    : NumStochOpt.QuasiFejer.proof_6_2_quasi_fejer_for_optimal_set
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T20:43:01.62026+00:00
-- url     : https://prove2.me/theorems/3f839fe5-2e95-429e-995b-73849e3b617e
-- title:
--   Proof of Theorem 6.2, p. 145 — the iterates of (6.11) form a stochastic quasi-Féjer sequence for X*
-- statement:
--   Let $X\subseteq\mathbb R^n$ be a nonempty convex compact set, $F:\mathbb R^n\to\mathbb R$, and $X^*$ the set of minimizers of $F$ over $X$. On a probability space let $x^0,x^1,\dots$ be measurable random vectors with $x^0\in X$, let $\xi^0(s)$ be integrable random directions, and let $\rho_s$, $\gamma_0(s)$ be random variables measurable with respect to $\sigma(x^0,\dots,x^s)$. Assume
--
--   1. (6.11): $x^{s+1}=\pi_X[x^s-\rho_s\xi^0(s)]$ for $s=0,1,\dots$;
--   2. (6.12): for every $x^*\in X^*$ and every $s$, almost surely
--   $$
--   F(x^*)-F(x^s)\ge\langle E\{\xi^0(s)\mid x^0,\dots,x^s\},x^*-x^s\rangle+\gamma_0(s);
--   $$
--   3. the parts of (6.15) used here: $\rho_s\ge0$ for all $s$ with probability 1, and
--   $$
--   \sum_{s=0}^\infty E\{\rho_s|\gamma_0(s)|+\rho_s^2\|\xi^0(s)\|^2\}<\infty .
--   $$
--
--   Then $\{x^s\}$ is a stochastic quasi-Féjer sequence (6.14) for the set $X^*$.
--
--   This is the step that places Theorem 6.2 inside the framework of Theorem 6.1: convergence of $\|x^*-x^s\|$ for every $x^*\in X^*$ and existence of accumulation points then follow from Theorem 6.1 (a), (b).
--
--   **Formalization Note** Convexity and continuity of $F$ and $\sum_s\rho_s=\infty$, assumed in Theorem 6.2, are not needed for this step and are omitted. The book's display before this sentence has an unspecified constant $C$; the quasi-Féjer property only requires some summable $r_s$, and $r_s=2\rho_s|\gamma_0(s)|+E\{\rho_s^2\|\xi^0(s)\|^2\mid x^0,\dots,x^s\}$ works. The error term $\gamma_0(s)$ does not depend on $x^*$ (see the Formalization Note of Theorem 6.2).
-- source:
--   Yu. Ermoliev, "Stochastic Quasigradient Methods", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 6, p. 145, Proof of Theorem 6.2, sentence after display 2 ("In view of (6.15) and by the definition (6.14) …")

import Mathlib
import Definitions.Def_NumStochOpt_QuasiFejer_ProjectionMethod
import Definitions.Def_NumStochOpt_QuasiFejer_StochQuasiFejer

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace NumStochOpt.QuasiFejer

/-- **The iterates form a stochastic quasi-Féjer sequence for `X*`** (Ermoliev, Ch. 6 of
Ermoliev & Wets (1988), proof of Theorem 6.2, p. 145, sentence after the second display).
For the stochastic quasigradient projection method (6.11) on a nonempty convex compact `X`, with
directions satisfying (6.12) for every `x* ∈ X*` and parameters satisfying `ρ_s ≥ 0` and
`∑_s E{ρ_s|γ₀(s)| + ρ_s²‖ξ⁰(s)‖²} < ∞` from (6.15), the sequence `{x^s}` is a stochastic
quasi-Féjer sequence (6.14) for the optimal set `X*`. -/
theorem proof_6_2_quasi_fejer_for_optimal_set {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (x ξ : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ρ γ₀ : ℕ → Ω → ℝ)
    (hXconv : Convex ℝ X) (hXcpt : IsCompact X) (hXne : X.Nonempty)
    (hx_meas : ∀ s, Measurable (x s)) (hx0 : ∀ ω, x 0 ω ∈ X)
    (hξ_int : ∀ s, Integrable (ξ s) μ)
    (hρ_adapt : ∀ s, StronglyMeasurable[historySigma x s] (ρ s))
    (hγ_adapt : ∀ s, StronglyMeasurable[historySigma x s] (γ₀ s))
    (hrec : ∀ s ω, x (s + 1) ω = projX X (x s ω - ρ s ω • ξ s ω))
    (hqg : ∀ xstar ∈ optimalSet F X, ∀ s, ∀ᵐ ω ∂μ,
      F xstar - F (x s ω) ≥ ⟪(condExp (historySigma x s) μ (ξ s)) ω, xstar - x s ω⟫_ℝ + γ₀ s ω)
    (hρ_nonneg : ∀ᵐ ω ∂μ, ∀ s, 0 ≤ ρ s ω)
    (hsum : ∑' s, ∫⁻ ω, ENNReal.ofReal (ρ s ω * |γ₀ s ω| + ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) ∂μ < ⊤) :
    IsStochQuasiFejer μ x (optimalSet F X) := by sorry

end NumStochOpt.QuasiFejer
