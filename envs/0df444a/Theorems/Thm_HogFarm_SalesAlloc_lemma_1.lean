-- Prove2me | Theorems.Thm_HogFarm_SalesAlloc_lemma_1
-- name    : HogFarm.SalesAlloc.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:56.146671+00:00
-- url     : https://prove2.me/theorems/f8fc283f-311f-4ed6-8e0c-d71330f7d7ae
-- title:
--   Lemma 1, p. 15 — concavity of value and action value
-- statement:
--   For every period $1\le t\le t_M$ and observed information state, the Bellman value is concave on nonnegative stocks. At fixed nonnegative stock, the action value is jointly concave in the two contract and two holding decisions when holdings are nonnegative:
--
--   $$V_t\text{ is concave in }(s^1,s^2),\qquad v_t\text{ is concave in }(y^1,y^2,z^1,z^2).$$
--
--   The first assertion appears in the induction claim of the proof; the second is Lemma 1's stated conclusion. They support the later holding-margin argument. **Formalization Note** Standing includes the disclosed bounds and measurability; the physical stock domain is nonnegative.
-- source:
--   Kouvelis, Liu, Qiu & Turcic, Managing Operations of a Hog Farm Facing Volatile Markets, SSRN preprint 3912801 (March 6, 2023), p. 15 (PDF 15), Lemma 1; pp. 38–39 (PDF 38–39), proof

import Mathlib
import Definitions.Def_HogFarm_SalesAlloc_Model

namespace HogFarm.SalesAlloc

/-- Lemma 1, p. 15, and the joint induction assertion in its proof, pp. 38–39. -/
theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (hS : M.Standing) (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ M.T) (ω : Ω) :
    ConcaveOn ℝ {s : ℝ × ℝ | 0 ≤ s.1 ∧ 0 ≤ s.2}
      (fun s => value M t s.1 s.2 ω) ∧
    ∀ s1 s2 : ℝ, 0 ≤ s1 → 0 ≤ s2 →
      ConcaveOn ℝ {a : (ℝ × ℝ) × (ℝ × ℝ) | 0 ≤ a.2.1 ∧ 0 ≤ a.2.2}
        (fun a => actionValue M t ω s1 s2 a.1.1 a.1.2 a.2.1 a.2.2) := by sorry

end HogFarm.SalesAlloc
