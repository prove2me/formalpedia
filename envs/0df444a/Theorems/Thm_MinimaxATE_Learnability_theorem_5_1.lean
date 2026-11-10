-- Prove2me | Theorems.Thm_MinimaxATE_Learnability_theorem_5_1
-- name    : MinimaxATE.Learnability.theorem_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:02:04.945698+00:00
-- url     : https://prove2.me/theorems/b92f124e-25b4-4c00-affc-e5f7753c61d9
-- title:
--   Theorem 5.1 — lower bound from symmetric mutual fat-shattering
-- statement:
--   Fix $c\in(0,1/2)$. There are constants $A_c,a_c,b_c>0$ depending only on $c$ such that the following holds for every measurable space $\mathcal X$, all classes $\mathcal P\subseteq[c,1-c]^{\mathcal X}$, $\mathcal M\subseteq[0,1]^{\mathcal X}$ and scales $\kappa,\gamma>0$. Let $k\ge1$ with $\mathrm{fat}^{\mathrm{sym\text{-}mut}}_{\kappa,\gamma}(\mathcal P,\mathcal M)>k$. For every accuracy $0<\varepsilon<b_c\kappa\gamma$ and every sample size
--   $$n\le a_c\,\frac{\kappa\gamma}\varepsilon\,\frac{k}{\log(2k)},$$
--   every measurable estimator $\hat\tau_n$ based on $n$ samples (with internal randomness) satisfies
--   $$\sup_{D\in\mathcal D(\mathcal P,\mathcal M,c)}\Pr_D\big[|\hat\tau_n-\tau_D|>\varepsilon\big]\ge\frac14-A_c\,\frac{\log^2(2k)}{\kappa^2\gamma k}.$$
--
--   The first lower bound of the paper, for classes with a symmetric shattering structure.
--
--   **Formalization Note.** The supremum is taken in $[0,\infty]$ over the class (it is $0$ for an empty class). Estimators are measurable functions of the sample and a uniform seed. As printed the statement is false over a $\sigma$-algebra that does not separate points (see the mission's findings); it is stated as printed, for every measurable space.
--
--   Differences from the source:
--   - reading: "Fix c, κ, γ; there are constants A_c, a_c, b_c that depend only on c" → the constants are chosen after c and before X, P, M, κ, γ, k, ε, n and the estimator; reason: the paper's convention for c-dependent constants.
--   - reading: τ̂_n → every measurable estimator based on n samples with internal randomness; reason: the lower bound is over the estimators of eq. (1).
--   - reading: concept classes P, M → P ⊆ [c, 1−c]^X, M ⊆ [0, 1]^X; reason: the standing setting of §3 (p. 18).
--   - encoding: sup_D Pr[|τ̂_n − τ_D| > ε] ≥ 1/4 − A_c log²(2k)/(κ²γk) → ENNReal.ofReal of the right-hand side ≤ the supremum in [0, ∞] of the measures of the failure sets; reason: Lean convention; ofReal of a negative number is 0, and a probability is ≥ 0, so the instances agree.
-- source:
--   Cai, Kalavasis, Mamali, Mehrotra, Zampetakis, Minimax Rates for Estimation of Average Treatment Effects in Observational Studies, STOC 2027 submission (manuscript sha256 89998c39…), p. 29 (PDF 31), Theorem 5.1

import Mathlib
import Definitions.Def_MinimaxATE_Learnability_SampleComplexity
import Definitions.Def_MinimaxATE_Learnability_FatDims

namespace MinimaxATE.Learnability

universe u

theorem theorem_5_1 : ∀ (c : ℝ), 0 < c → c < 1 / 2 →
    ∃ A a b : ℝ, 0 < A ∧ 0 < a ∧ 0 < b ∧
    ∀ (X : Type u) [MeasurableSpace X] (P M : Set (X → ℝ)),
      (∀ p ∈ P, ∀ x, p x ∈ Set.Icc c (1 - c)) → (∀ m ∈ M, ∀ x, m x ∈ Set.Icc (0 : ℝ) 1) →
    ∀ (κ γ : ℝ), 0 < κ → 0 < γ →
    ∀ (k : ℕ), 1 ≤ k → (k : ℕ∞) < symFat P M κ γ →
    ∀ (ε : ℝ), 0 < ε → ε < b * κ * γ →
    ∀ (n : ℕ), (n : ℝ) ≤ a * (κ * γ / ε) * ((k : ℝ) / Real.log (2 * k)) →
    ∀ τhat : (Fin n → Obs X) × ℝ → ℝ, Measurable τhat →
      ENNReal.ofReal (1 / 4 - A * Real.log (2 * k) ^ 2 / (κ ^ 2 * γ * k)) ≤
        ⨆ D ∈ DClass P M c, failureProb D n τhat ε := by sorry

end MinimaxATE.Learnability
