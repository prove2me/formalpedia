-- Prove2me | Theorems.Thm_GEPPGrowth_Main_lemma_4_2
-- name    : GEPPGrowth.Main.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:38:21.246354+00:00
-- url     : https://prove2.me/theorems/decf720a-6cf1-4ae1-a102-5282ec4a4946
-- title:
--   Lemma 4.2 — Standard Gaussian small interval
-- statement:
--   Let $x\sim N(0,1)$. Then, for every $t>0$,
--
--   $$
--   \Pr(|x|\le t)\le t\sqrt{\dfrac{2}{\pi}}
--   $$.
--
--   This controls small one-dimensional Gaussian intervals.
--
--   Differences from the source:
--   - encoding: standard normal random variables → probabilities under the canonical standard normal law; reason: depends only on the distribution, with the same closed events and constants
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), Lemma 4.2, printed p.8, PDF p.9

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Lemma 4.2, printed p.8 / PDF p.9. -/
theorem lemma_4_2 (t : ℝ) (ht : 0 < t) :
    prob (gaussianReal 0 1) {x | |x| ≤ t} ≤ t * Real.sqrt (2 / Real.pi) := by sorry

end GEPPGrowth.Main
