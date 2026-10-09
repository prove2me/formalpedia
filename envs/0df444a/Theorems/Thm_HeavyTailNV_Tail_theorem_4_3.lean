-- Prove2me | Theorems.Thm_HeavyTailNV_Tail_theorem_4_3
-- name    : HeavyTailNV.Tail.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:23:17.63651+00:00
-- url     : https://prove2.me/theorems/8db645de-e9a9-4ebd-b9ed-c8d18900f920
-- title:
--   Theorem 4.3 — heavy-tailed law represents worst-case shortage
-- statement:
--   Let $\alpha>1$, $m_1>0$, and $m_\alpha>m_1^\alpha$, and let $\Pi_{1,\alpha}$ be the worst-case expected shortage over nonnegative demand laws with those two moments. First,
--
--   $$\Pi_{1,\alpha}\in RV_{-(\alpha-1)}.$$
--
--   Second, there exists a nonnegative probability law $F^*\notin\mathcal F_{1,\alpha}$ such that, for every $q\ge0$,
--
--   $$\mathbb E_{F^*}[(\tilde d^*-q)^+]=\Pi_{1,\alpha}(q),\qquad\bar F^*\in RV_{-\alpha}.$$
--
--   For every real $0\le a<\alpha$, its $a$th moment is finite, while for every $a\ge\alpha$ its $a$th moment is infinite. Thus a single heavy-tailed demand law reproduces the robust shortage at all admissible order quantities, though it cannot belong to the original ambiguity set.
--
--   **Formalization Note** The law is explicitly supported on $[0,\infty)$, as the paper's nonnegative demand convention requires. Finite shortage expectations are explicit. Moments use extended nonnegative integrals so infinity is represented faithfully. The paper's proof constant $C_3$ on p. 30 is positive only when $\alpha>2$; the stated moment conclusion remains the theorem's target for all $\alpha>1$.
-- source:
--   Das, Dhara and Natarajan, On the heavy-tail behavior of the distributionally robust newsvendor, arXiv:1806.05379v2, pp. 27–28, Theorem 4.3

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model

namespace HeavyTailNV.Tail

open MeasureTheory Filter

theorem theorem_4_3 (α m1 ma : ℝ) (hα : 1 < α) (hm1 : 0 < m1)
    (hma : m1 ^ α < ma) :
    IsRegularlyVarying (worstCase m1 ma α) (-(α - 1)) ∧
    ∃ Fstar : Measure ℝ, IsProbabilityMeasure Fstar ∧
      Fstar (Set.Iio 0) = 0 ∧ Fstar ∉ ambiguitySet m1 ma α ∧
      (∀ q : ℝ, 0 ≤ q →
        Integrable (fun w : ℝ => max (w - q) 0) Fstar ∧
        (∫ w, max (w - q) 0 ∂Fstar) = worstCase m1 ma α q) ∧
      IsRegularlyVarying (tail Fstar) (-α) ∧
      (∀ a : ℝ, 0 ≤ a → a < α →
        (∫⁻ w, ENNReal.ofReal (w ^ a) ∂Fstar) < ⊤) ∧
      (∀ a : ℝ, α ≤ a →
        (∫⁻ w, ENNReal.ofReal (w ^ a) ∂Fstar) = ⊤) := by sorry

end HeavyTailNV.Tail
