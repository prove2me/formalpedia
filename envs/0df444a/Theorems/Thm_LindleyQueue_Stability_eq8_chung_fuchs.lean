-- Prove2me | Theorems.Thm_LindleyQueue_Stability_eq8_chung_fuchs
-- name    : LindleyQueue.Stability.eq8_chung_fuchs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:36:41.032525+00:00
-- url     : https://prove2.me/theorems/78d3cb00-f3ff-4e57-b74e-ac64180da7b1
-- title:
--   Eq. (8) (Chung–Fuchs, cited) — a mean-zero non-lattice random walk comes within $\epsilon$ of every $x$ infinitely often
-- statement:
--   Let $X_1, X_2, \dots$ be independent, identically distributed, integrable real random variables on a probability space, with
--
--   $$
--   \mathscr{E}(X_1) = 0,
--   $$
--
--   and suppose that not all values assumed by $X_1$ are integral multiples of a fixed number: there is no $d > 0$ such that $X_1 \in d\mathbb Z$ almost surely. Let $U_n = X_1 + \dots + X_n$. Then for every real $x$ and every $\epsilon > 0$,
--
--   $$
--   p(|U_n - x| < \epsilon \text{ for an infinity of } n) = 1.
--   $$
--
--   This is the non-lattice case of the recurrence theorem of Chung and Fuchs (1951), which Lindley quotes as eq. (8) and uses for the critical case $\mathscr{E}(u) = 0$ of the stability theorem. The non-lattice hypothesis excludes in particular $X_1 = 0$ almost surely.
--
--   **Formalization Note** The statement is made for an arbitrary i.i.d. integrable sequence (Lindley applies it to $u_r = s_r - t_r$, which is such a sequence under Assumptions 1–2), so it is more general than the page, not less. The lattice half of the page's remark ("If $u$ only assumes integral multiples of a fixed number then (8) only holds for $x$ having these values") is not formalized: it needs the span of the lattice made explicit. Indices are $0$-based: $U_n = \sum_{i < n} X_i$.
-- source:
--   Lindley (Proc. Camb. Phil. Soc. 48, 1952), §4, eq. (8), p. 281 (Chung and Fuchs, cited: Mem. Amer. Math. Soc. 6, 1951)

import Mathlib
import Definitions.Def_LindleyQueue_Stability_Model
open MeasureTheory ProbabilityTheory Filter Topology

namespace LindleyQueue.Stability

/-- Eq. (8), p. 281 (Chung and Fuchs, cited by Lindley), non-lattice case: for an i.i.d.
integrable sequence with mean zero whose values are not almost surely all integral multiples of
one fixed positive number, the partial sums come within `ε` of every `x` infinitely often,
almost surely. -/
theorem eq8_chung_fuchs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hint : Integrable (X 0) P)
    (hmean : ∫ ω, X 0 ω ∂P = 0)
    (hnonlattice : ¬ ∃ d : ℝ, 0 < d ∧ ∀ᵐ ω ∂P, ∃ k : ℤ, X 0 ω = k * d)
    (x : ℝ) (ε : ℝ) (hε : 0 < ε) :
    P {ω | ∃ᶠ n in atTop, |(∑ i ∈ Finset.range n, X i ω) - x| < ε} = 1 := by sorry

end LindleyQueue.Stability
