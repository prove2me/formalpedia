-- Prove2me | Theorems.Thm_MultiperiodRisk_Bellman_lemma_3_1
-- name    : MultiperiodRisk.Bellman.lemma_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:06:27.496985+00:00
-- url     : https://prove2.me/theorems/6ae633fc-3447-46c8-8689-a19518c45526
-- title:
--   Lemma 3.1 — stability splits density ratios at intermediate stopping times
-- statement:
--   Let $\mathcal P$ be a stable closed convex set of test probabilities on $(\Omega,\mathcal F_N)$, absolutely continuous with respect to $\mathbb P_0$, and let $\tau\le\sigma\le\nu$ be stopping times with values in $\{0,\dots,N\}$. For $\mathbb Q\in\mathcal P^e$ write $Z$ for its density martingale. Then
--   $$
--   \Bigl\{\Bigl(\frac{Z_\nu}{Z_\sigma},\frac{Z_\sigma}{Z_\tau}\Bigr)\Bigm| Z\in\mathcal P^e\Bigr\}=\Bigl\{\Bigl(\frac{Z'_\nu}{Z'_\sigma},\frac{Z_\sigma}{Z_\tau}\Bigr)\Bigm| Z\in\mathcal P^e,\ Z'\in\mathcal P^e\Bigr\},
--   $$
--   as sets of pairs of random variables identified up to $\mathbb P_0$-null sets.
--
--   Concretely: (a) every pair on the left is on the right, and (b) for all $Z,Z'\in\mathcal P^e$ there is $Z''\in\mathcal P^e$ with $Z''_\nu/Z''_\sigma=Z'_\nu/Z'_\sigma$ and $Z''_\sigma/Z''_\tau=Z_\sigma/Z_\tau$ a.s.
--
--   The lemma rephrases stability: the conditional behaviour of a test probability after $\sigma$ can be chosen independently of its behaviour between $\tau$ and $\sigma$. It is used in step (3) of the proof of Theorem 4.2.
--
--   **Formalization Note** The members of the sets are ratios of conditional expectations, hence a.e.-classes; equality of sets is stated as the two inclusions up to a.e. equality. Ratios use real division, which is harmless because $Z>0$ a.s. for $Z\in\mathcal P^e$.
-- source:
--   Artzner, Delbaen, Eber, Heath, Ku, Coherent Multiperiod Risk Adjusted Values and Bellman's Principle, Ann. Oper. Res. 152 (2007); manuscript of Nov. 16, 2004, p. 10, Lemma 3.1

import Mathlib
import Definitions.Def_MultiperiodRisk_Bellman_TestSet

namespace MultiperiodRisk.Bellman

open MeasureTheory

/-- Lemma 3.1: for a stable set and stopping times `τ ≤ σ ≤ ν`,
`{(Z_ν/Z_σ, Z_σ/Z_τ) | Z ∈ 𝒫ᵉ} = {(Z'_ν/Z'_σ, Z_σ/Z_τ) | Z, Z' ∈ 𝒫ᵉ}`, as sets of
`P₀`-a.e. classes of pairs. -/
theorem lemma_3_1 {Ω : Type*} {m : MeasurableSpace Ω} (P₀ : Measure Ω)
    [IsProbabilityMeasure P₀] (ℱ : Filtration ℕ m) (N : ℕ) (D : TestSet P₀ ℱ N)
    (hstab : IsStable D) (τ σ ν : Ω → WithTop ℕ) (hτ : IsBddStoppingTime ℱ N τ)
    (hσ : IsBddStoppingTime ℱ N σ) (hν : IsBddStoppingTime ℱ N ν)
    (hτσ : ∀ ω, τ ω ≤ σ ω) (hσν : ∀ ω, σ ω ≤ ν ω) :
    (∀ f ∈ Pe D, ∃ g ∈ Pe D, ∃ g' ∈ Pe D,
      (fun ω => stoppedValue (Z P₀ ℱ f) ν ω / stoppedValue (Z P₀ ℱ f) σ ω) =ᵐ[P₀]
        (fun ω => stoppedValue (Z P₀ ℱ g') ν ω / stoppedValue (Z P₀ ℱ g') σ ω) ∧
      (fun ω => stoppedValue (Z P₀ ℱ f) σ ω / stoppedValue (Z P₀ ℱ f) τ ω) =ᵐ[P₀]
        (fun ω => stoppedValue (Z P₀ ℱ g) σ ω / stoppedValue (Z P₀ ℱ g) τ ω)) ∧
    (∀ f ∈ Pe D, ∀ f' ∈ Pe D, ∃ g ∈ Pe D,
      (fun ω => stoppedValue (Z P₀ ℱ g) ν ω / stoppedValue (Z P₀ ℱ g) σ ω) =ᵐ[P₀]
        (fun ω => stoppedValue (Z P₀ ℱ f') ν ω / stoppedValue (Z P₀ ℱ f') σ ω) ∧
      (fun ω => stoppedValue (Z P₀ ℱ g) σ ω / stoppedValue (Z P₀ ℱ g) τ ω) =ᵐ[P₀]
        (fun ω => stoppedValue (Z P₀ ℱ f) σ ω / stoppedValue (Z P₀ ℱ f) τ ω)) := by sorry

end MultiperiodRisk.Bellman
