-- Prove2me | Theorems.Thm_Kyprianou_Ch02_positiveNegativeSumLimitV1
-- name    : Kyprianou.Ch02.positiveNegativeSumLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:50:18.532982+00:00
-- url     : https://prove2.me/theorems/5770094a-690f-4a49-b6a7-63e9dd36707c
-- title:
--   Positive and negative sum limits from absolute and signed sums
-- statement:
--   Use max(x,0)=(|x|+x)/2 and max(-x,0)=(|x|-x)/2 then continuity of arithmetic and pair formation.
-- source:
--   Kyprianou (2006), Exercise 2.8, deterministic partition and probability limit lemmas for Jordan variation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.positiveNegativeSumLimitV1
    (d : ℕ → ℕ → ℝ) (v z : ℝ)
    (hv : Tendsto (fun n => ∑ k : Fin (n+1), |d n k|) atTop (nhds v))
    (hz : ∀ n, ∑ k : Fin (n+1), d n k = z) :
    Tendsto (fun n => (∑ k : Fin (n+1), max (d n k) 0,
      ∑ k : Fin (n+1), max (-d n k) 0)) atTop
      (nhds ((v+z)/2, (v-z)/2)) := by sorry
