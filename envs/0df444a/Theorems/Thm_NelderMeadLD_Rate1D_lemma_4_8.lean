-- Prove2me | Theorems.Thm_NelderMeadLD_Rate1D_lemma_4_8
-- name    : NelderMeadLD.Rate1D.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:13:22.038775+00:00
-- url     : https://prove2.me/theorems/cb4d147a-4275-429c-82e6-0eeb07926e08
-- title:
--   Lemma 4.8, p. 133 — with ρ = 1, the diameter shrinks by a factor φ < 1, depending only on χ and γ, between consecutive contractions
-- statement:
--   Fix $\chi > 1$ and $0 < \gamma < 1$. There is a number $\varphi < 1$, depending only on $\chi$ and $\gamma$, with the following property. Let $0 < \sigma < 1$, let $f:\mathbb R \to \mathbb R$ be strictly convex with bounded level sets, and apply the one-dimensional Nelder–Mead method with $\rho = 1$ and coefficients $\chi, \gamma, \sigma$ to $f$, starting from a nondegenerate ordered initial interval $\Delta_0$. If iterations $k < k'$ are contractions and no iteration strictly between them is a contraction, then the simplex $\Delta = \Delta_{k+1}$ immediately following contraction $k$ and the simplex $\Delta' = \Delta_{k'+1}$ immediately following the next contraction $k'$ satisfy
--   $$\operatorname{diam}(\Delta') \le \varphi\, \operatorname{diam}(\Delta).$$
--
--   This is the per-cycle contraction factor of the move-sequence analysis; Theorem 4.2 follows by chaining these cycles.
--
--   **Formalization Note.** "Depending only on $\chi$ and $\gamma$" is encoded by the quantifier order: $\varphi$ is chosen after $\chi, \gamma$ and before $\sigma$, $f$ and $\Delta_0$. $\Delta_k$ is the simplex at the start of iteration $k$, so the simplex immediately following iteration $k$ is $\Delta_{k+1}$.
-- source:
--   Lagarias, Reeds, Wright & Wright, Convergence properties of the Nelder–Mead simplex method in low dimensions, SIAM J. Optim. 9 (1998), p. 133, Lemma 4.8

import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm
import Definitions.Def_NelderMeadLD_Rate1D_Algorithm

namespace NelderMeadLD.Rate1D

open NelderMeadLD.Conv1D

theorem lemma_4_8 :
    ∀ χ γ : ℝ, 1 < χ → 0 < γ → γ < 1 →
      ∃ φ : ℝ, φ < 1 ∧
        ∀ σ : ℝ, 0 < σ → σ < 1 →
        ∀ f : ℝ → ℝ, StrictConvexOn ℝ Set.univ f →
        (∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ}) →
        ∀ p0 : ℝ × ℝ, IsStart f p0 →
        ∀ k k' : ℕ, k < k' →
          IsContraction (moveAt f χ γ σ p0 k) →
          IsContraction (moveAt f χ γ σ p0 k') →
          (∀ i : ℕ, k < i → i < k' → ¬ IsContraction (moveAt f χ γ σ p0 i)) →
          diam (run f 1 χ γ σ p0 (k' + 1)) ≤ φ * diam (run f 1 χ γ σ p0 (k + 1)) := by sorry

end NelderMeadLD.Rate1D
