-- Prove2me | Theorems.Thm_LogSupermodularBIS_Main_Supplement_lemma_A_5
-- name    : LogSupermodularBIS.Main.Supplement.lemma_A_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:33:54.442189+00:00
-- url     : https://prove2.me/theorems/7ef77c1d-b4c2-4303-91ff-458f6d22462e
-- title:
--   Lemma A.5 — accumulated conditional simulation error
-- statement:
--   Consider an ideal and an implemented randomized procedure with a shared initial law and at most $t$ sequential steps. Let $\eta_0,\ldots,\eta_{t-1}$ be deterministic nonnegative error bounds. Conditional on every common past, suppose the ideal and implemented output laws at step $j$ have total variation distance at most $\eta_j$. Then their final outputs satisfy
--   $$
--   \|\mathcal L(\mathrm{ideal\ output})-\mathcal L(\mathrm{implemented\ output})\|_{\rm TV}
--   \le\sum_{j=0}^{t-1}\eta_j.
--   $$
--   This is the error-accumulation interface for capped finite-precision simulation; successive transitions may be fully adaptive.
--
--   **Formalization Note** Histories are arbitrary measurable states, transitions are probability kernels, and the final output is any common measurable function of the state. Early stopping is padded by absorbing transitions.
--
--   Differences from the source:
--   - encoding: at most t sequential steps conditional on every common past → t measurable probability-kernel transitions on complete histories, from one common initial probability measure, followed by a common measurable output map; reason: complete-history state represents adaptive procedures; absorbing transitions pad early stopping; measurable laws are the standing convention
--   - encoding: step indices j≤t → zero-based indices 0≤j<t; reason: exactly the same t step errors
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 41 (PDF 42), Lemma A.5

import Mathlib
import Definitions.Def_LogSupermodularBIS_Main_Supplement_Sequential

open MeasureTheory ProbabilityTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main.Supplement

/-- Lemma A.5, p.41 (PDF 42): conditional simulation errors accumulate additively.
`H` stores the complete past, and the hypothesis holds at every common history. -/
theorem lemma_A_5 {H Y : Type*} [MeasurableSpace H] [MeasurableSpace Y]
    (μ : Measure H) [IsProbabilityMeasure μ] (K L : ℕ → Kernel H H)
    [∀ j, IsMarkovKernel (K j)] [∀ j, IsMarkovKernel (L j)]
    (t : ℕ) (η : ℕ → ℝ) (hη : ∀ j < t, 0 ≤ η j)
    (hstep : ∀ j < t, ∀ h : H, EventTVLE (K j h) (L j h) (η j))
    (out : H → Y) (hout : Measurable out) :
    EventTVLE ((sequentialLaw K μ t).map out) ((sequentialLaw L μ t).map out)
      (∑ j ∈ Finset.range t, η j) := by sorry

end LogSupermodularBIS.Main.Supplement
