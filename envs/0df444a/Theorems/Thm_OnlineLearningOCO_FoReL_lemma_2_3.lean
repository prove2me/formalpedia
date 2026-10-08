-- Prove2me | Theorems.Thm_OnlineLearningOCO_FoReL_lemma_2_3
-- name    : OnlineLearningOCO.FoReL.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:24.374008+00:00
-- url     : https://prove2.me/theorems/00e898af-22bd-486c-b948-9313f2ebe44f
-- title:
--   Lemma 2.3 — the regret of FoReL is at most R(u) − R(w₁) plus its stability
-- statement:
--   Let $S$ be a set, $f_1, f_2, \dots : S \to \mathbb R$ arbitrary loss functions and $R : S \to \mathbb R$ an arbitrary regularization function, and let $w_1, w_2, \dots$ be a run of Follow-the-Regularized-Leader, $w_t \in \operatorname{argmin}_{w \in S} \sum_{i<t} f_i(w) + R(w)$. Then for every horizon $T \ge 0$ and every $u \in S$,
--
--   $$
--   \sum_{t=1}^{T} \big(f_t(w_t) - f_t(u)\big) \le R(u) - R(w_1) + \sum_{t=1}^{T} \big(f_t(w_t) - f_t(w_{t+1})\big).
--   $$
--
--   The lemma reduces bounding the regret of FoReL to bounding how much consecutive predictions differ in loss; Theorem 2.11 combines it with the stability bound of Lemma 2.10.
--
--   **Formalization Note** No convexity, continuity or structure is assumed: the lemma holds for arbitrary $f_t$ and $R$, as on the page. Rounds are 1-based.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 128, Lemma 2.3

import Mathlib
import Definitions.Def_OnlineLearningOCO_FoReL_IsFoReLRun

namespace OnlineLearningOCO.FoReL

/-- Lemma 2.3 (Shalev-Shwartz, FnT ML 4(2) (2011), p. 128). Let `w₁, w₂, …` be the sequence
of vectors produced by FoReL. Then for all `u ∈ S`,
`∑_{t=1}^T (f_t(w_t) − f_t(u)) ≤ R(u) − R(w_1) + ∑_{t=1}^T (f_t(w_t) − f_t(w_{t+1}))`.
No convexity or structure is needed: `f` and `R` are arbitrary real functions. -/
theorem lemma_2_3 {E : Type*} (S : Set E) (f : ℕ → E → ℝ) (R : E → ℝ) (w : ℕ → E)
    (hw : IsFoReLRun S f R w) (T : ℕ) :
    ∀ u ∈ S,
      ∑ t ∈ Finset.Icc 1 T, (f t (w t) - f t u)
        ≤ R u - R (w 1) + ∑ t ∈ Finset.Icc 1 T, (f t (w t) - f t (w (t + 1))) := by sorry

end OnlineLearningOCO.FoReL
