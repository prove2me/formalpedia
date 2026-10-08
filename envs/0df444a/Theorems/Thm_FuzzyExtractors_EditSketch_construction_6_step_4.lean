-- Prove2me | Theorems.Thm_FuzzyExtractors_EditSketch_construction_6_step_4
-- name    : FuzzyExtractors.EditSketch.construction_6_step_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:41.587232+00:00
-- url     : https://prove2.me/theorems/b9381bc2-cec9-47d5-b85f-9a8a840862b3
-- title:
--   Construction 6, step 4 — if $\mathrm{dis}(w, w') \le t$ then $\mathrm{supp}(v) = w \triangle w'$
-- statement:
--   Let $K$ be a finite field of characteristic $2$, $t \ge 0$, and $w, w', v \subseteq K^*$. Suppose $|w \triangle w'| \le t$, $|v| \le t$, and $v$ has the odd syndromes computed in step 2 of PinSketch's recovery:
--   $$\sum_{x \in v} x^{2j+1} = \sum_{x \in w'} x^{2j+1} - \sum_{x \in w} x^{2j+1} \qquad (0 \le j < t).$$
--   Then
--   $$v = w \triangle w'.$$
--
--   This is the correctness claim of step 4 of Construction 6: the set recovered by syndrome decoding is the symmetric difference, so $w = w' \triangle v$.
--
--   **Formalization Note.** Indices are 0-based: entry $j$ is the paper's $\sigma_{2j+1}$, for the paper's $\sigma_1, \sigma_3, \dots, \sigma_{2t-1}$. Subtraction is in $K$, where it coincides with addition.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors, arXiv:cs/0602007v4, Construction 6 (PinSketch), recovery step 4, p. 23

import Mathlib
import Definitions.Def_FuzzyExtractors_EditSketch_Basic

namespace FuzzyExtractors.EditSketch

theorem construction_6_step_4 {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [CharP K 2] (t : ℕ) (w w' v : Finset Kˣ) (hdis : symmDiffDis w w' ≤ t) (hv : v.card ≤ t)
    (hsyn : ∀ j : Fin t,
      syn (2 * (j : ℕ) + 1) v = syn (2 * (j : ℕ) + 1) w' - syn (2 * (j : ℕ) + 1) w) :
    v = symmDiff w w' := by sorry

end FuzzyExtractors.EditSketch
