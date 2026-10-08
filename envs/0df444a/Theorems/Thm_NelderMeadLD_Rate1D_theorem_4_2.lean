-- Prove2me | Theorems.Thm_NelderMeadLD_Rate1D_theorem_4_2
-- name    : NelderMeadLD.Rate1D.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:13:56.498772+00:00
-- url     : https://prove2.me/theorems/cc33a048-c6d6-4dc6-8e55-c45b3979cb07
-- title:
--   Theorem 4.2, p. 130 — in dimension 1 with ρ = 1, diam(Δ_{k+M}) ≤ ½ diam(Δ_k) for all k ≥ K, M depending only on χ and γ
-- statement:
--   Fix an expansion coefficient $\chi > 1$ and a contraction coefficient $0 < \gamma < 1$. There is an integer $M \ge 0$, depending only on $\chi$ and $\gamma$, with the following property.
--
--   Let $0 < \sigma < 1$, let $f:\mathbb R \to \mathbb R$ be strictly convex with bounded level sets, and apply the one-dimensional Nelder–Mead method with reflection coefficient $\rho = 1$ and coefficients $\chi, \gamma, \sigma$ to $f$, starting from a nondegenerate ordered initial interval $\Delta_0$. Then the iteration index $K$ of Lemma 4.2 exists — that is, there is a first iteration $K$ with $f_1^{(K)} \le f_e^{(K)}$ — and
--   $$\operatorname{diam}(\Delta_{k+M}) \le \tfrac12 \operatorname{diam}(\Delta_k)\qquad\text{for all } k \ge K.$$
--
--   Here $\Delta_k = \{x_1^{(k)}, x_2^{(k)}\}$ is the interval at iteration $k$, $\operatorname{diam}(\Delta_k) = |x_1^{(k)} - x_2^{(k)}|$, and $f_e^{(K)}$ is the value of $f$ at the expansion point $x_1^{(K)} + \chi(x_1^{(K)} - x_2^{(K)})$. The theorem says that, once the minimizer is bracketed, the Nelder–Mead interval converges M-step linearly, with a step count $M$ that does not depend on $f$ or on the initial interval.
--
--   **Formalization Note.** "$M$ depending only on $\chi$ and $\gamma$" is encoded by the quantifier order: $M$ is chosen after $\chi, \gamma$ and before $\sigma$, $f$ and $\Delta_0$. The page presupposes the index $K$ of Lemma 4.2; here its existence is part of the conclusion, so the statement cannot hold vacuously for a run that is never bracketed. This makes the item slightly stronger than the printed sentence (the existence is Lemma 4.2, proved in the paper). The shrink coefficient $\sigma$ is a parameter of the algorithm and satisfies (2.1); it does not otherwise enter.
-- source:
--   Lagarias, Reeds, Wright & Wright, Convergence properties of the Nelder–Mead simplex method in low dimensions, SIAM J. Optim. 9 (1998), p. 130, Theorem 4.2

import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm
import Definitions.Def_NelderMeadLD_Rate1D_Algorithm

namespace NelderMeadLD.Rate1D

open NelderMeadLD.Conv1D

theorem theorem_4_2 :
    ∀ χ γ : ℝ, 1 < χ → 0 < γ → γ < 1 →
      ∃ M : ℕ,
        ∀ σ : ℝ, 0 < σ → σ < 1 →
        ∀ f : ℝ → ℝ, StrictConvexOn ℝ Set.univ f →
        (∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ}) →
        ∀ p0 : ℝ × ℝ, IsStart f p0 →
        ∃ K : ℕ, FirstBracket f χ γ σ p0 K ∧
          ∀ k : ℕ, K ≤ k →
            diam (run f 1 χ γ σ p0 (k + M)) ≤ 1 / 2 * diam (run f 1 χ γ σ p0 k) := by sorry

end NelderMeadLD.Rate1D
