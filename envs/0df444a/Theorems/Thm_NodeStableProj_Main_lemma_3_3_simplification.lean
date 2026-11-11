-- Prove2me | Theorems.Thm_NodeStableProj_Main_lemma_3_3_simplification
-- name    : NodeStableProj.Main.lemma_3_3_simplification
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:58:54.408261+00:00
-- url     : https://prove2.me/theorems/aae198cf-4afe-4c6f-bc0c-976a730d6ec5
-- title:
--   Lemma 3.3, closing sentence — under ε̃ = O(1/√D̂), ε = O(ε̃√(D̂ ln(1/δ)))
-- statement:
--   Let $c_1>0$ be a constant for which Lemma 3.6 holds. Assuming $\tilde\varepsilon=O(1/\sqrt{\hat D})$, the $\varepsilon$ of Lemma 3.3 item 3 simplifies to $\varepsilon=O(\tilde\varepsilon\sqrt{\hat D\ln(1/\delta)})$: for every $a>0$ there is $C>0$ such that for all integers $0<D<\hat D$, $\tilde\varepsilon>0$, $\delta\in(0,1)$ and $n$ satisfying the hypotheses of item 3 (the gap $\hat D-D\ge2c_1\log(9n/\delta)/\tilde\varepsilon$ and $\varepsilon\le1$) and $\tilde\varepsilon\sqrt{\hat D}\le a$,
--   $$\tilde\varepsilon\sqrt{2\hat D\ln(3/\delta)}+\hat D\,\tilde\varepsilon\,\frac{e^{\tilde\varepsilon}-1}{e^{\tilde\varepsilon}+1}\ \le\ C\,\tilde\varepsilon\sqrt{\hat D\ln(1/\delta)} .$$
--
--   This is the form in which the stability parameter is usually quoted.
--
--   Differences from the source:
--   - reading: "Assuming ε̃ = O(1/√D̂), this simplifies to ε = O(ε̃√(D̂ ln(1/δ)))" → ∀ a > 0, ∃ C > 0, for all parameters satisfying item 3's hypotheses with ε̃√D̂ ≤ a: ε ≤ C ε̃ √(D̂ ln(1/δ)); reason: O(·) read with universal constants; as printed (see finding I1)
-- source:
--   Aden-Ali, Sealfon, Smith, Steinke, Ullman, Node Differential Privacy via Node-Stable Graph Projections, STOC 2027 submission (manuscript sha256 42f18565…), p. 12, Lemma 3.3 item 3, closing sentence

import Mathlib
import Definitions.Def_NodeStableProj_Main_Projection

open MeasureTheory

namespace NodeStableProj.Main

/-- Lemma 3.3, closing sentence of item 3, p. 12: "Assuming `ε̃ = O(1/√D̂)`, this simplifies to
`ε = O(ε̃ √(D̂ ln(1/δ)))`" — for every `a > 0` there is `C > 0` such that under the hypotheses of
item 3 (with a constant `c1` of Lemma 3.6) and `ε̃ √D̂ ≤ a`, the `ε` of item 3 is at most
`C ε̃ √(D̂ ln(1/δ))`. -/
theorem lemma_3_3_simplification (c1 : ℝ) (hc1 : 0 < c1) (hacc : SVTAccuracy c1)
    (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D Dhat : ℕ) (εt δ : ℝ) (n : ℕ),
      0 < D → D < Dhat → 0 < εt → 0 < δ → δ < 1 →
      2 * c1 * Real.log (9 * n / δ) / εt ≤ (Dhat : ℝ) - D →
      stabEps Dhat εt δ ≤ 1 →
      εt * Real.sqrt Dhat ≤ a →
      stabEps Dhat εt δ ≤ C * (εt * Real.sqrt (Dhat * Real.log (1 / δ))) := by sorry

end NodeStableProj.Main
