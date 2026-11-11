-- Prove2me | Theorems.Thm_LogSupermodularBIS_Main_lemma_4_2
-- name    : LogSupermodularBIS.Main.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:48.365579+00:00
-- url     : https://prove2.me/theorems/45504ddf-1e3a-471d-9a16-835ede0bfec5
-- title:
--   Lemma 4.2 — bin scores
-- statement:
--   Let $d\ge2$, and let $m$ and $A_0=\log m+1$ be as in (4.1). The bin scores $\bar a_j=m[H(j/m)-H((j+1)/m)]$ satisfy
--   $$\max_j|\bar a_j|\le A_0\qquad\text{and}\qquad E|a(U_1)-\bar a_{Y_1}|\le\frac{2\log m+6}{m},$$
--   where $U_1$ is uniform on $(0,1)$ and $Y_1=\lfloor mU_1\rfloor$.
--
--   Differences from the source: none.
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 21 (PDF 22), Lemma 4.2

import Definitions.Def_LogSupermodularBIS_Main_Interaction

open MeasureTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-- Lemma 4.2 (Bin scores), p. 21, with `m` and `A_0` of (4.1). -/
theorem lemma_4_2 (d : ℕ) (hd : 2 ≤ d) :
    (∀ j : Fin (numBins d), |binScore (numBins d) j| ≤ paramA0 d) ∧
    (∫ u in Set.Ioo (0 : ℝ) 1, |logit u - binScoreAt (numBins d) u|) ≤
      (2 * Real.log (numBins d) + 6) / (numBins d) := by sorry

end LogSupermodularBIS.Main
