-- Prove2me | Theorems.Thm_MarginalDRO_Lagrange_sec_3_1_measurable_selection
-- name    : MarginalDRO.Lagrange.sec_3_1_measurable_selection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:45.327661+00:00
-- url     : https://prove2.me/theorems/311ec4b2-f7cc-4bee-9d67-4f1a24ff18c8
-- title:
--   §3.1, p. 13 — the optimal-solution multifunction x^OPT(c) = argmax_{x∈𝒳} cᵀx has a measurable selection x*
-- statement:
--   Let $\mathcal X \subset \mathbb R^n$ be a nonempty finite set and let $x^{OPT}(c) := \arg\max_{x\in\mathcal X} c^T x$. There is a Borel measurable map $x^* : \mathbb R^n \to \mathbb R^n$ with $x^*(c) \in x^{OPT}(c)$ for every $c$, that is,
--   $$x^*(c) \in \mathcal X \quad\text{and}\quad \sum_{i=1}^n c_i x_i \le \sum_{i=1}^n c_i\, x^*_i(c) \quad \text{for all } x \in \mathcal X .$$
--
--   The selection $x^*$ turns any joint law $\theta$ of $\tilde c$ into a joint law of $(\tilde c, x^*(\tilde c))$, which is how the proof of Theorem 2 bounds $E_\theta Z$ by the coupling form.
-- source:
--   Chen, Ma, Natarajan, Simchi-Levi & Yan, preprint (2018), p. 13, §3.1 (measurable selection of x^OPT)

import Mathlib
import Definitions.Def_MarginalDRO_Lagrange_Model

open MeasureTheory ProbabilityTheory

namespace MarginalDRO.Lagrange

/-- §3.1, p. 13: a measurable selection `x*` of the optimal-solution multifunction `x^OPT`. -/
theorem sec_3_1_measurable_selection {n : ℕ} (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) :
    ∃ xstar : (Fin n → ℝ) → (Fin n → ℝ), Measurable xstar ∧
      ∀ c, xstar c ∈ 𝒳 ∧ ∀ x ∈ 𝒳, ∑ i, c i * x i ≤ ∑ i, c i * xstar c i := by sorry
end MarginalDRO.Lagrange
