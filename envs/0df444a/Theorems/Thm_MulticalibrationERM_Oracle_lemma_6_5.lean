-- Prove2me | Theorems.Thm_MulticalibrationERM_Oracle_lemma_6_5
-- name    : MulticalibrationERM.Oracle.lemma_6_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:52:52.058893+00:00
-- url     : https://prove2.me/theorems/13c85b1a-8c1f-4a23-81b3-6bcab0a3ba82
-- title:
--   Lemma 6.5 — coverage of the confidence intervals
-- statement:
--   Draw a confidence sample of $n_{\mathrm{conf}}$ independent labeled examples from $D$; let $O$ be the inputs that occur, $n_x$ their counts, $\hat y_x$ their mean outcomes, $\iota=\max\{1,\log(8n_{\mathrm{conf}}/\delta_0)\}$, $r_x=\min\{1,\sqrt{\iota/n_x}\}$ and $I_x=[\hat y_x-r_x,\hat y_x+r_x]\cap[0,1]$, $\delta_0\in(0,1)$. With probability at least $1-\delta_0$, $f^\star(x)\in I_x$ for every $x\in O$ (of positive mass).
--
--   Differences from the source:
--   - reading: f⋆(x) = E[Y | X = x] for x ∈ O → the condition f⋆(x) ∈ I_x is imposed (or asserted) at the inputs x ∈ O with D_X({x}) > 0; f⋆ is defined at atoms as E[Y 1{X = x}]/D_X({x}); reason: a conditional mean is determined only up to D_X-null sets, so at an input of mass zero its value is not determined; at atoms it is
--   - encoding: the confidence sample → the first n_conf examples of an i.i.d. stream from D; reason: the law of the first n_conf coordinates is the i.i.d. law
--   - encoding: probability of the failure event → the measure applied to the failure set, i.e. its outer measure when the set is not measurable; reason: equal to the probability when the event is measurable; an outer-measure bound is never weaker
-- source:
--   Okoroafor, The Sample Complexity of Multicalibration with an ERM Oracle, supplied 61-page preprint (PDF SHA256 654c7a8127547d76c5a4b6db236ce672c2c09a70d21d56a3981583e1805d0f8d; exact arXiv revision unresolved, not arXiv:2610.14363v1), p. 34, Lemma 6.5

import Mathlib
import Definitions.Def_MulticalibrationERM_Oracle_Setting
import Definitions.Def_MulticalibrationERM_Oracle_OEMC

open MeasureTheory ProbabilityTheory

namespace MulticalibrationERM.Oracle

/-- Lemma 6.5 (p. 34): coverage of the confidence intervals. From a confidence sample of `n_conf`
i.i.d. examples (`s 0, …, s (n_conf − 1)` of an i.i.d. stream from `D`), with `O` the inputs that
occur, `n_x` their counts, `ŷ_x` their average outcomes, `ι = max{1, log(8 n_conf/δ₀)}`,
`r_x = min{1, √(ι/n_x)}` and `I_x = [ŷ_x − r_x, ŷ_x + r_x] ∩ [0, 1]`: with probability at least
`1 − δ₀`, `f⋆(x) ∈ I_x` for every `x ∈ O` (at every `x ∈ O` of positive mass, where
`f⋆(x) = E[Y | X = x]` is determined). -/
theorem lemma_6_5 {X : Type} [MeasurableSpace X] [DecidableEq X] (D : LabeledDist X)
    (nconf : ℕ) (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hδ₀' : δ₀ < 1) :
    (Measure.infinitePi fun _ : ℕ => D.μ)
        {s | ∃ x ∈ confSet s nconf, 0 < D.atom x ∧
          D.fstar x ∉ Set.Icc (confLo s nconf δ₀ x) (confHi s nconf δ₀ x)} ≤
      ENNReal.ofReal δ₀ := by sorry

end MulticalibrationERM.Oracle
