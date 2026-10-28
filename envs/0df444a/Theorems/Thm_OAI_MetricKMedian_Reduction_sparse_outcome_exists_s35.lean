-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Reduction_sparse_outcome_exists_s35
-- name    : OAI.MetricKMedian.Reduction.sparse_outcome_exists_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:41:46.015638+00:00
-- url     : https://prove2.me/theorems/65cde98d-82dd-4540-84a5-3a1fa2d905fd
-- title:
--   OAI.MetricKMedian.Reduction.sparse_outcome_exists_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Reduction`, with `open Finset`):
--
--   ```lean
--   theorem sparse_outcome_exists_s35 (F O T : Finset (Fin I.n)) (hOF : O ⊆ F)
--       (hO : O.Nonempty) (hk : O.card=I.k) (hTF : T ⊆ F) (hT : T.Nonempty)
--       (α η : ℝ) (δ : ℚ) (c b : ℕ) (hc : 0 < c) (hδ : 0 < (δ:ℝ))
--       (hsmall : (δ:ℝ) ≤ 1/6) (hη : 0 < η) (hC : 0 < cost I O)
--       (hcost : cost I T ≤ α*cost I O) (hcard : T.card ≤ I.k+c)
--       (hsp : Sparse (I:=I) F O ((δ:ℝ)*η/(2*c)))
--       (hfactor : 1+12*(δ:ℝ) ≤ α+η) (hb : 6*(α+η)*c/((δ:ℝ)*η) ≤ (b:ℝ)) :
--       ∃ S ∈ sparseOutcomes I F T δ c b,
--         S ⊆ F ∧ S.Nonempty ∧ S.card ≤ I.k ∧ cost I S ≤ (α+η)*cost I O
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Reduction.Sparse` (definitions bundle `OAIQ035K026` of this split); `OAI.MetricKMedian.Reduction.sparseOutcomes` (definitions bundle `OAIQ035K044` of this split); `OAI.MetricKMedian.Instance` and `OAI.MetricKMedian.cost` (the published bundle `Def_MetricKMedian`).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Reduction.Program.ordinarySet_spec_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K044

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}

theorem sparse_outcome_exists_s35 (F O T : Finset (Fin I.n)) (hOF : O ⊆ F)
    (hO : O.Nonempty) (hk : O.card=I.k) (hTF : T ⊆ F) (hT : T.Nonempty)
    (α η : ℝ) (δ : ℚ) (c b : ℕ) (hc : 0 < c) (hδ : 0 < (δ:ℝ))
    (hsmall : (δ:ℝ) ≤ 1/6) (hη : 0 < η) (hC : 0 < cost I O)
    (hcost : cost I T ≤ α*cost I O) (hcard : T.card ≤ I.k+c)
    (hsp : Sparse (I:=I) F O ((δ:ℝ)*η/(2*c)))
    (hfactor : 1+12*(δ:ℝ) ≤ α+η) (hb : 6*(α+η)*c/((δ:ℝ)*η) ≤ (b:ℝ)) :
    ∃ S ∈ sparseOutcomes I F T δ c b,
      S ⊆ F ∧ S.Nonempty ∧ S.card ≤ I.k ∧ cost I S ≤ (α+η)*cost I O := by
  sorry

end MetricKMedian.Reduction
end
end

end OAI
end
