-- Prove2me | Theorems.Thm_MultiperiodRisk_Bellman_lemma_4_1
-- name    : MultiperiodRisk.Bellman.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:06:56.282984+00:00
-- url     : https://prove2.me/theorems/631a50be-5ffe-41c9-b8da-33dddb43be00
-- title:
--   Lemma 4.1 — for stable $\mathcal P$ the family defining $\Psi_\sigma$ is closed under minima and maxima
-- statement:
--   Let $\mathcal P$ be a stable closed convex set of test probabilities on $(\Omega,\mathcal F_N)$, absolutely continuous with respect to $\mathbb P_0$, let $X$ be a value process and $\sigma$ a stopping time with values in $\{0,\dots,N\}$. Let
--   $$
--   S_\sigma=\bigl\{\mathbb E_{\mathbb Q}[X_\tau\mid\mathcal F_\sigma]\ \bigm|\ \sigma\le\tau\le N\text{ stopping time},\ \mathbb Q\in\mathcal P^e\bigr\}.
--   $$
--   For all $h_1,h_2\in S_\sigma$ there are $h,h'\in S_\sigma$ with $h=h_1\wedge h_2$ and $h'=h_1\vee h_2$ $\mathbb P_0$-a.s.
--
--   Closure under minima makes $S_\sigma$ directed downward, which is what lets its essential infimum be approached by a decreasing sequence; this gives the Corollary and step (3) of the proof of Theorem 4.2.
--
--   **Formalization Note** "Closed" is closure up to $\mathbb P_0$-null sets, since the members are conditional expectations defined up to null sets.
-- source:
--   Artzner, Delbaen, Eber, Heath, Ku, Coherent Multiperiod Risk Adjusted Values and Bellman's Principle, Ann. Oper. Res. 152 (2007); manuscript of Nov. 16, 2004, p. 11, Lemma 4.1

import Mathlib
import Definitions.Def_MultiperiodRisk_Bellman_Psi

namespace MultiperiodRisk.Bellman

open MeasureTheory

/-- Lemma 4.1: for a stable set and a stopping time `σ`, the family
`{𝐄_ℚ[X_τ | ℱ_σ] | τ ≥ σ, ℚ ∈ 𝒫ᵉ}` is closed (up to `P₀`-null sets) under pointwise
minima and maxima. -/
theorem lemma_4_1 {Ω : Type*} {m : MeasurableSpace Ω} (P₀ : Measure Ω)
    [IsProbabilityMeasure P₀] (ℱ : Filtration ℕ m) (N : ℕ) (D : TestSet P₀ ℱ N)
    (hstab : IsStable D) (X : ℕ → Ω → ℝ) (hX : IsValueProcess P₀ ℱ N X)
    (σ : Ω → WithTop ℕ) (hσ : IsBddStoppingTime ℱ N σ) :
    ∀ h₁ ∈ psiFamily D X σ hσ.1, ∀ h₂ ∈ psiFamily D X σ hσ.1,
      (∃ h ∈ psiFamily D X σ hσ.1, h =ᵐ[P₀] fun ω => min (h₁ ω) (h₂ ω)) ∧
      (∃ h ∈ psiFamily D X σ hσ.1, h =ᵐ[P₀] fun ω => max (h₁ ω) (h₂ ω)) := by sorry

end MultiperiodRisk.Bellman
