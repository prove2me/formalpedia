-- Prove2me | Theorems.Thm_HermiteLaptop_MaxAgree_lemma_4_2
-- name    : HermiteLaptop.MaxAgree.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:18:27.473573+00:00
-- url     : https://prove2.me/theorems/9f2340b8-05e6-4a86-83ce-4a56884f1e9a
-- title:
--   Lemma 4.2 — certified bounds (25) and (26) imply the positive- and negative-edge inequalities
-- statement:
--   Let $M\in\mathbb N_0$, let $\underline P_M,\overline P_M$ be as in Corollary 2.5 (for a mixture and bounds $\underline c_{k,m}\le c_{k,m}\le\overline c_{k,m}$, $k\in\mathcal K$, $m\le M$), and let $a\in[-1/2,0]$ and $\gamma\ge0$.
--   - If $\underline P_M(\rho)\ge\gamma s^+_a(\rho)$ for all $\rho\in[a,1]$ (25), then the positive-edge inequality $P(\rho)\ge\gamma s^+_a(\rho)$ holds for all $\rho\in[a,1]$.
--   - If $1-\overline P_M(a)\ge\gamma$ (26), then the negative-edge inequality $1-P(a)\ge\gamma$ holds.
--
--   **Formalization Note.** The two clauses are a conjunction of implications; the hypotheses of Corollary 2.5 (bounds, summability) are carried.
--
--   Differences from the source:
--   - reading: "Recall P̲_M(ρ) and P̄_M(ρ) defined in Corollary 2.5" → the hypotheses of Corollary 2.5 (bounds for k ∈ K, m ≤ M) are hypotheses here; reason: P̲_M, P̄_M are defined only in that setting
--   - encoding: P̲_M = Σ_{k∈K} λ_k P̲_{k,M}, P̄_M = Σ_{k∈K} λ_k P̄_{k,M} (series over a possibly infinite K) → hypotheses that both series are summable on [−1, 1]; reason: for arbitrary bounds the printed series may diverge and P̲_M, P̄_M are then undefined; the hypothesis excludes only that case (automatic for finite K)
--   - encoding: mixture probabilities (λ_k)_{k∈K} and its collision probability P → Mixture with λ : ℕ → ℝ zero off K, HasSum λ 1, P = Σ_k λ_k P_k; reason: law of total probability; K may be infinite
-- source:
--   García-Soriano, Miyauchi, Hermite Brings a Laptop, arXiv:2609.35453 (held version, sha256 97504f90…), p. 27 (PDF 30), Lemma 4.2

import Mathlib
import Definitions.Def_HermiteLaptop_MaxAgree_Instance
import Definitions.Def_HermiteLaptop_MaxAgree_Hermite
import Definitions.Def_HermiteLaptop_MaxAgree_TruncBounds

namespace HermiteLaptop.MaxAgree

/-- Lemma 4.2: (25) `P̲_M(ρ) ≥ γ s⁺_a(ρ)` on `[a, 1]` gives the positive-edge inequality, and
(26) `1 − P̄_M(a) ≥ γ` gives the negative-edge inequality. -/
theorem lemma_4_2 (M : ℕ) (μ : Mixture) (cl cu : ℕ → ℕ → ℝ)
    (hcl : ∀ k ∈ μ.K, ∀ m ≤ M, cl k m ≤ coeffC k m)
    (hcu : ∀ k ∈ μ.K, ∀ m ≤ M, coeffC k m ≤ cu k m)
    (hsumL : ∀ ρ ∈ Set.Icc (-1 : ℝ) 1,
      Summable (fun k : ℕ => μ.lam k * truncLower M (cl k) (cu k) ρ))
    (hsumU : ∀ ρ ∈ Set.Icc (-1 : ℝ) 1,
      Summable (fun k : ℕ => μ.lam k * truncUpper M (cl k) (cu k) ρ))
    (a : ℝ) (ha : a ∈ Set.Icc (-1 / 2 : ℝ) 0) (γ : ℝ) (hγ : 0 ≤ γ) :
    ((∀ ρ ∈ Set.Icc a 1, γ * sPlus a ρ ≤ μ.truncLower M cl cu ρ) →
        ∀ ρ ∈ Set.Icc a 1, γ * sPlus a ρ ≤ μ.collision ρ) ∧
    (γ ≤ 1 - μ.truncUpper M cl cu a → γ ≤ 1 - μ.collision a) := by sorry

end HermiteLaptop.MaxAgree
