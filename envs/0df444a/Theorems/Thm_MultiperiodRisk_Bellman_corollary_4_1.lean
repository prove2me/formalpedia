-- Prove2me | Theorems.Thm_MultiperiodRisk_Bellman_corollary_4_1
-- name    : MultiperiodRisk.Bellman.corollary_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:07:29.413986+00:00
-- url     : https://prove2.me/theorems/afd5e4a8-a203-40fe-91fb-7273bda21950
-- title:
--   Corollary of Lemma 4.1 — expectations of $\Psi_\sigma(X)$ under any $\mu\ll\mathbb P_0$
-- statement:
--   Let $\mathcal P$ be a stable closed convex set of test probabilities on $(\Omega,\mathcal F_N)$, absolutely continuous with respect to $\mathbb P_0$, with $\mathcal P^e\ne\emptyset$. Let $X$ be a value process, $\sigma$ a stopping time with values in $\{0,\dots,N\}$ and $\mu$ any probability measure with $\mu\ll\mathbb P_0$ (not necessarily in $\mathcal P$). Then
--   $$
--   \mathbb E_\mu\bigl[\Psi_\sigma(X)\bigr]=\inf\bigl\{\mathbb E_\mu\bigl[\mathbb E_{\mathbb Q}[X_\tau\mid\mathcal F_\sigma]\bigr]\ \bigm|\ \mathbb Q\in\mathcal P^e,\ \sigma\le\tau\le N\text{ stopping time}\bigr\}.
--   $$
--
--   Expectation under $\mu$ thus commutes with the essential infimum defining $\Psi_\sigma(X)$. This is how the proof of Theorem 4.2, step (3), exchanges an inner essential infimum and an outer conditional expectation.
--
--   **Formalization Note** The page prints the left-hand essential infimum over $\mathbb Q\in\mathcal P^e$ only, leaving $\tau$ free; the right-hand side and the use in step (3) range over $\mathbb Q$ and $\tau\ge\sigma$, so the left-hand side is $\mathbb E_\mu[\Psi_\sigma(X)]$. The infimum on the right is over a nonempty family of reals bounded below by $-\sup_n\|X_n\|_\infty$, so the real infimum is the true one.
-- source:
--   Artzner, Delbaen, Eber, Heath, Ku, Coherent Multiperiod Risk Adjusted Values and Bellman's Principle, Ann. Oper. Res. 152 (2007); manuscript of Nov. 16, 2004, p. 11, Corollary (of Lemma 4.1)

import Mathlib
import Definitions.Def_MultiperiodRisk_Bellman_Psi

namespace MultiperiodRisk.Bellman

open MeasureTheory

/-- Corollary of Lemma 4.1: for a stable set, a stopping time `σ` and a probability
`μ ≪ P₀`, `𝐄_μ[Ψ_σ(X)] = inf {𝐄_μ[𝐄_ℚ[X_τ | ℱ_σ]] | ℚ ∈ 𝒫ᵉ, τ ≥ σ}`. -/
theorem corollary_4_1 {Ω : Type*} {m : MeasurableSpace Ω} (P₀ : Measure Ω)
    [IsProbabilityMeasure P₀] (ℱ : Filtration ℕ m) (N : ℕ) (D : TestSet P₀ ℱ N)
    (hstab : IsStable D) (hPe : (Pe D).Nonempty) (X : ℕ → Ω → ℝ)
    (hX : IsValueProcess P₀ ℱ N X) (σ : Ω → WithTop ℕ) (hσ : IsBddStoppingTime ℱ N σ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hμ : μ ≪ P₀) :
    ∫ ω, Psi D X σ hσ.1 ω ∂μ =
      ⨅ p : {p : (Ω → WithTop ℕ) × (Ω → ℝ) //
          IsBddStoppingTime ℱ N p.1 ∧ (∀ ω, σ ω ≤ p.1 ω) ∧ p.2 ∈ Pe D},
        ∫ ω, (Q P₀ p.1.2)[stoppedValue X p.1.1 | hσ.1.measurableSpace] ω ∂μ := by sorry

end MultiperiodRisk.Bellman
