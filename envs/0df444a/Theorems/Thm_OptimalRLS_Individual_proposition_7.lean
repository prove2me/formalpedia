-- Prove2me | Theorems.Thm_OptimalRLS_Individual_proposition_7
-- name    : OptimalRLS.Individual.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:19:11.617145+00:00
-- url     : https://prove2.me/theorems/0cb0b030-5b09-44d0-834d-e6e05f5d111b
-- title:
--   Proposition 7, pp. 25–26 — the Bayes error for a random sign observed in Gaussian noise is Φ(−‖g‖/σ)
-- statement:
--   Let $g \in \mathbb R^\ell$ and $\sigma > 0$. Let $s$ be a random sign with $P[s = +1] = P[s = -1] = 1/2$, and let $n = (n_i)_{i=1}^\ell$ be independent $\mathcal N(0, \sigma^2)$ variables, independent of $s$. Observe $y = s g + n$.
--
--   For a measurable decision rule $D : \mathbb R^\ell \to \{+1, -1\}$, the error probability is
--   $$P[D(y) \ne s] = \tfrac12 P[D(g + n) \ne 1] + \tfrac12 P[D(-g + n) \ne -1].$$
--   Every such rule satisfies $P[D(y) \ne s] \ge \Phi(-\|g\|/\sigma)$, and some rule attains equality, so
--   $$\min_{D : \mathbb R^\ell \to \{+1, -1\}} P[D(y) \neq s] = \Phi\Big(-\frac{\|g\|}{\sigma}\Big).$$
--   Here $\|g\| = (\sum_i g_i^2)^{1/2}$ and $\Phi$ is the standard normal distribution function.
--
--   This is the one-dimensional testing problem to which the proof of Theorem 3 reduces the estimation of each sign $s_n$.
--
--   **Formalization Note** "min" is stated as a lower bound for every rule together with a rule that attains it. The noise law is the product of `gaussianReal 0 σ²` over `Fin ℓ`. Decision rules are measurable real-valued maps taking only the values $\pm 1$.
-- source:
--   Caponnetto & De Vito, Found. Comput. Math. 7 (2007), authors' copy, Proposition 7, pp. 25–26 (quoted from Györfi et al., Lemma 3.2)

import Mathlib
import Definitions.Def_OptimalRLS_Individual_Model

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal

namespace OptimalRLS.Individual

/-- **Proposition 7** (p. 25–26; Györfi et al., Lemma 3.2). Let `g ∈ ℝ^ℓ`, `s` a fair random sign,
and `n = (n_i)_{i=1}^ℓ` independent `N(0, σ²)` variables independent of `s`; set `y = s g + n`.
Then the error probability of the Bayes decision for `s` based on `y` is
`min_{D : ℝ^ℓ → {+1,−1}} P[D(y) ≠ s] = Φ(−‖g‖/σ)`.

Encoding: conditioning on `s`, `P[D(y) ≠ s] = ½ μ{n | D(g + n) ≠ 1} + ½ μ{n | D(−g + n) ≠ −1}`
with `μ = N(0, σ²)^{⊗ℓ}`; decision rules are measurable `{+1, −1}`-valued maps; "min" is stated as
a lower bound for every rule together with a rule attaining it. `‖g‖ = (∑ g_i²)^{1/2}`. -/
theorem proposition_7 (ℓ : ℕ) (g : Fin ℓ → ℝ) (σ : ℝ) (hσ : 0 < σ) :
    let μ : Measure (Fin ℓ → ℝ) := Measure.pi fun _ : Fin ℓ => gaussianReal 0 (σ ^ 2).toNNReal
    let errProb : ((Fin ℓ → ℝ) → ℝ) → ℝ≥0∞ := fun D =>
      (1 / 2 : ℝ≥0∞) * μ {n | D (g + n) ≠ 1} + (1 / 2 : ℝ≥0∞) * μ {n | D (-g + n) ≠ -1}
    (∀ D : (Fin ℓ → ℝ) → ℝ, Measurable D → (∀ y, D y = 1 ∨ D y = -1) →
        ENNReal.ofReal (Phi (-(Real.sqrt (∑ i, g i ^ 2) / σ))) ≤ errProb D) ∧
      ∃ D : (Fin ℓ → ℝ) → ℝ, Measurable D ∧ (∀ y, D y = 1 ∨ D y = -1) ∧
        errProb D = ENNReal.ofReal (Phi (-(Real.sqrt (∑ i, g i ^ 2) / σ))) := by sorry

end OptimalRLS.Individual
