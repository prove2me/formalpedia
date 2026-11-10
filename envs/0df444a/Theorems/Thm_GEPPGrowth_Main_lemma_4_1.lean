-- Prove2me | Theorems.Thm_GEPPGrowth_Main_lemma_4_1
-- name    : GEPPGrowth.Main.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:38:49.053116+00:00
-- url     : https://prove2.me/theorems/e63699a1-d8bf-4925-ae01-79349ffee25c
-- title:
--   Lemma 4.1 — Gaussian absolute tail with Mills prefactor
-- statement:
--   Let $x\sim N(0,1)$. Then, for every $t>0$,
--
--   $$
--   \Pr(|x|\ge t)\le\dfrac{\sqrt2}{t\sqrt\pi}\exp\left(-\dfrac{t^2}{2}\right)
--   $$.
--
--   This retains the exact two-sided Mills prefactor.
--
--   Differences from the source:
--   - encoding: standard normal random variables → probabilities under the canonical standard normal law; reason: depends only on the distribution, with the same closed events and constants
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), Lemma 4.1, printed p.7, PDF p.8

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Lemma 4.1, printed p.7 / PDF p.8. Two-sided absolute Gaussian tail with the exact Mills prefactor. -/
theorem lemma_4_1 (t : ℝ) (ht : 0 < t) :
    prob (gaussianReal 0 1) {x | t ≤ |x|} ≤
      Real.sqrt 2 / (t*Real.sqrt Real.pi) * Real.exp (-t^2/2) := by sorry

end GEPPGrowth.Main
