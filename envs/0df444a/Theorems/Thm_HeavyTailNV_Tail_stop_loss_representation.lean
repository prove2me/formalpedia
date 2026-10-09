-- Prove2me | Theorems.Thm_HeavyTailNV_Tail_stop_loss_representation
-- name    : HeavyTailNV.Tail.stop_loss_representation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:23:44.743366+00:00
-- url     : https://prove2.me/theorems/2122fc31-05c2-4c2c-a96f-be02b239c19d
-- title:
--   (2.1) — representation by a single demand law
-- statement:
--   For the nonnegative moment ambiguity set $\mathcal F_{1,\alpha}$ with $\alpha>1$, $m_1>0$, and $m_\alpha>m_1^\alpha$, there is a single nonnegative probability law $F^*$ whose expected shortage agrees with the worst-case shortage at every real threshold:
--
--   $$\mathbb E_{F^*}[(\tilde d^*-q)^+]=\Pi_{1,\alpha}(q),\qquad q\in\mathbb R.$$
--
--   This specializes the representation (2.1) to the paper's ambiguity set. The expectation is finite for every $q$; for $q\le0$ both sides equal $m_1-q$.
-- source:
--   Das, Dhara and Natarajan, On the heavy-tail behavior of the distributionally robust newsvendor, arXiv:1806.05379v2, p. 6, (2.1), specialized to (3.1); p. 29, use of (2.1)

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model

namespace HeavyTailNV.Tail

open MeasureTheory

theorem stop_loss_representation (α m1 ma : ℝ) (hα : 1 < α)
    (hm1 : 0 < m1) (hma : m1 ^ α < ma) :
    ∃ Fstar : Measure ℝ, IsProbabilityMeasure Fstar ∧
      Fstar (Set.Iio 0) = 0 ∧
      ∀ q : ℝ, Integrable (fun w : ℝ => max (w - q) 0) Fstar ∧
        (∫ w, max (w - q) 0 ∂Fstar) = worstCase m1 ma α q := by sorry

end HeavyTailNV.Tail
