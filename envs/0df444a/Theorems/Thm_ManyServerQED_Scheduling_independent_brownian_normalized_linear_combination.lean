-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_independent_brownian_normalized_linear_combination
-- name    : ManyServerQED.Scheduling.independent_brownian_normalized_linear_combination
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T01:05:56.709085+00:00
-- url     : https://prove2.me/theorems/03c8f064-e1f1-5d1e-b36a-02a33b5158b5
-- title:
--   Normalized combinations of independent Brownian motions
-- statement:
--   Let $B$ and $C$ be independent real standard Brownian motions. A linear combination $aB+bC$ with $a^2+b^2=1$ is a real standard Brownian motion.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem ManyServerQED.Scheduling.independent_brownian_normalized_linear_combination {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (B C : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hC : IsBrownianReal C P)
    (hI : IndepFun (fun ω t => B t ω) (fun ω t => C t ω) P)
    (a b : ℝ) (hW : a^2+b^2=1) :
    IsBrownianReal (fun t ω => a*B t ω+b*C t ω) P := by sorry
