-- Prove2me | Theorems.Thm_LogSupermodularBIS_Main_lemma_5_7
-- name    : LogSupermodularBIS.Main.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:54.700193+00:00
-- url     : https://prove2.me/theorems/0cf74fcc-3fbc-4fdb-97b9-4dd0f0648b7c
-- title:
--   Lemma 5.7 — moments of a smoothed indicator
-- statement:
--   Let $0<w\le1/2$. For every $c\in[0,1]$, with $p=1-c$, the smoothed indicator $\phi_c=\tfrac12\mathbf 1_{[c-h(c),1)}+\tfrac12\mathbf 1_{[c+h(c),1)}$ of a uniform input on $(0,1)$ satisfies
--   $$E\phi_c=p,\qquad\mathrm{Var}(\phi_c)=\Bigl(1-\frac w2\Bigr)p(1-p).\tag{5.9}$$
--
--   Differences from the source: none.
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 28 (PDF 29), Lemma 5.7, (5.9)

import Definitions.Def_LogSupermodularBIS_Main_Smoothing

open MeasureTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-- Lemma 5.7 (Moments of a smoothed indicator), p. 28. -/
theorem lemma_5_7 (w : ℝ) (hw : w ∈ Set.Ioc (0 : ℝ) (1 / 2)) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    (∫ u in Set.Ioo (0 : ℝ) 1, smoothedIndicator w c u) = 1 - c ∧
    (∫ u in Set.Ioo (0 : ℝ) 1, smoothedIndicator w c u ^ 2) -
        (∫ u in Set.Ioo (0 : ℝ) 1, smoothedIndicator w c u) ^ 2 =
      (1 - w / 2) * (1 - c) * (1 - (1 - c)) := by sorry

end LogSupermodularBIS.Main
