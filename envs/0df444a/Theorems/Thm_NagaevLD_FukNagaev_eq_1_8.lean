-- Prove2me | Theorems.Thm_NagaevLD_FukNagaev_eq_1_8
-- name    : NagaevLD.FukNagaev.eq_1_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:06.931056+00:00
-- url     : https://prove2.me/theorems/f7b1606a-73d1-4a80-8968-a7e44de8e409
-- title:
--   (1.8), p. 749 — P(S_n ≥ x) ≤ P(S̃_n ≥ x) + Σ P(X_i > y_i)
-- statement:
--   Let $X_1,\dots,X_n$ be independent random variables, $x>0$, and $y_1,\dots,y_n>0$. Let $\tilde X_i=X_i$ if $X_i\le y_i$ and $\tilde X_i=0$ otherwise, and $\tilde S_n=\sum_i\tilde X_i$. Then
--   $$P(S_n\ge x)\le P(\tilde S_n\ge x)+\sum_{i=1}^nP(X_i>y_i).$$
--
--   This is the truncation step of the proof of the Fuk–Nagaev inequality: it reduces the tail of $S_n$ to the tail of a sum of summands bounded above by $y_i$, at the cost of the probabilities that some summand exceeds its level.
--
--   **Formalization Note** Indices run over `Fin n`. The standing assumptions of the paper (independence, measurability, $x>0$, $y_i>0$) are kept as hypotheses although the inequality does not need them.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 749, proof of Theorem 1.3, (1.8)

import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

theorem eq_1_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (hx : 0 < x) (yv : Fin n → ℝ) (hyv : ∀ i, 0 < yv i) :
    P.real {ω | x ≤ S n X ω} ≤
      P.real {ω | x ≤ St X yv ω} + ∑ i, P.real {ω | yv i < X i ω} := by sorry

end NagaevLD.FukNagaev
