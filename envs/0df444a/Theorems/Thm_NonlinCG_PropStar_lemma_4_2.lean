-- Prove2me | Theorems.Thm_NonlinCG_PropStar_lemma_4_2
-- name    : NonlinCG.PropStar.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:49.717052+00:00
-- url     : https://prove2.me/theorems/b1cb921f-f569-4cf8-b7cc-adcced7dcfc6
-- title:
--   Lemma 4.2 — with Property (*), more than half of the steps in some block of Δ iterates exceed λ, beyond every index
-- statement:
--   Let $f$ satisfy Assumptions 2.1 at the starting point $x_1$ and let $(x_k, d_k, \beta_k, \alpha_k)$ be a run of the conjugate gradient iteration (1.2)–(1.3) with a line search such that
--
--   1. all iterates stay in the level set: $x_k \in \mathcal L$ for all $k \ge 1$ (4.4);
--   2. the Zoutendijk condition (2.7) holds;
--   3. the sufficient descent condition $\langle g_k, d_k\rangle \le -\sigma_3\|g_k\|^2$ holds for all $k \ge 1$ (4.1), with $0 < \sigma_3 \le 1$.
--
--   Assume the method has Property (\*), and that $\|g_k\| \ge \gamma > 0$ for all $k \ge 1$ (4.3). Then there exists $\lambda > 0$ such that for every $\Delta \in \mathbb N^*$ and every index $k_0$ there is an index $k \ge k_0$ with
--
--   $$|\mathcal K^\lambda_{k,\Delta}| > \frac{\Delta}{2},$$
--
--   where $\mathcal K^\lambda_{k,\Delta}$ is the set of indices $i$ with $k \le i \le k+\Delta-1$, $i \ge 2$ and $\|s_{i-1}\| = \|x_i - x_{i-1}\| > \lambda$.
--
--   In words: beyond any point, some block of $\Delta$ consecutive iterates contains more than $\Delta/2$ steps longer than $\lambda$, and $\lambda$ does not depend on $\Delta$. This is the second ingredient of the proof of Theorem 4.3. No sign condition on $\beta_k$ is assumed. As with Lemma 4.1, the hypotheses are steps of a proof by contradiction and may be unsatisfiable on every actual run.
--
--   **Formalization Note** Global continuous differentiability of $f$ (the paper's "$f$ is smooth", (1.1)) is assumed in addition to Assumptions 2.1. $|\mathcal K^\lambda_{k,\Delta}| > \Delta/2$ is written in natural numbers as $\Delta < 2|\mathcal K^\lambda_{k,\Delta}|$. The quantifier order is the paper's: $\lambda$ is chosen first, then $\Delta$ and $k_0$ are arbitrary.
-- source:
--   Gilbert & Nocedal, Global convergence properties of conjugate gradient methods for optimization, INRIA Rapport de Recherche 1268 (June 1990), HAL inria-00075291v1, p. 14, Lemma 4.2; 𝒦^λ_{k,Δ} on p. 14; (4.4) on p. 11

import Mathlib
import Definitions.Def_NonlinCG_PropStar_Setting

namespace NonlinCG.PropStar

/-- Lemma 4.2 (p. 14). Under Assumptions 2.1, for a run of (1.2)–(1.3) with a line search
satisfying (4.4), the Zoutendijk condition (2.7) and the sufficient descent condition (4.1), with
Property (*), and with (4.3), there is `λ > 0` such that for every `Δ ≥ 1` and every index `k₀`
some `k ≥ k₀` has `|𝒦^λ_{k,Δ}| > Δ/2`. No sign condition on `β_k` is assumed. -/
theorem lemma_4_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (β α : ℕ → ℝ) (x d : ℕ → E) (σ₃ : ℝ)
    (hA : NonlinCG.FRBound.Assumptions21 f (x 1)) (hrun : NonlinCG.FRBound.IsCGRun f β α x d)
    (hL : ∀ k ≥ 1, x k ∈ NonlinCG.FRBound.levelSet f (x 1))
    (hZ : NonlinCG.FRBound.ZoutendijkCondition f x d)
    (hσ₃ : 0 < σ₃ ∧ σ₃ ≤ 1) (hD : SufficientDescent f σ₃ x d)
    (hP : PropertyStar f β x)
    (h43 : ∃ γ > 0, ∀ k ≥ 1, γ ≤ ‖NonlinCG.FRBound.g f x k‖) :
    ∃ lam > 0, ∀ Δ : ℕ, 1 ≤ Δ → ∀ k₀ : ℕ, ∃ k ≥ k₀, Δ < 2 * (Kset lam x k Δ).card := by sorry

end NonlinCG.PropStar
