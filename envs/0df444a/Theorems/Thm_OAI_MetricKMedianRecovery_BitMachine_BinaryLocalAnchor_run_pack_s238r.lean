-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryLocalAnchor_run_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.run_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:03:38.885134+00:00
-- url     : https://prove2.me/theorems/6b9fc26c-fd8f-447c-958a-7cbc3c693853
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.run_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Geometry/LocalFuel.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/LocalFuel.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor`, with `open WordOperations WordList BinaryArithmetic RationalLeaves Polynomial`, `open BinaryFiniteContext (labels setBits)`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma run_pack_s238r {m d : ℕ} (δ : Fin m→Fin m→ℕ) (loc : Fin d→Fin m)
--       (hloc : Function.Injective loc) (fs : List (Fin m)) (r : ℕ) :
--       run (pack (fun i j=>(δ (loc j) i:ℚ)) fs r)=
--         setBits ((LocalSearch.executableDescent fs (LocalSearch.natCost δ (Finset.univ.image loc)) 5
--           (fuelPoly.eval (pack (fun i j=>(δ (loc j) i:ℚ)) fs r).length) (fs.take r).toFinset).image original)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.LocalSearch.executableDescent` and `OAI.MetricKMedianRecovery.LocalSearch.natCost` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.original` (definitions bundle `Q238L008` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.fuelPoly` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.setBits` (definitions bundle `Q238L025` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.pack` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.run` (definitions bundle `Q238L037` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.produce_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/LocalFuel.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.run_pack)

import Mathlib
import Definitions.Def_Q238L037

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalAnchor
open WordOperations WordList BinaryArithmetic RationalLeaves Polynomial
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] Take.run BinaryLabel.sort
lemma run_pack_s238r {m d : ℕ} (δ : Fin m→Fin m→ℕ) (loc : Fin d→Fin m)
    (hloc : Function.Injective loc) (fs : List (Fin m)) (r : ℕ) :
    run (pack (fun i j=>(δ (loc j) i:ℚ)) fs r)=
      setBits ((LocalSearch.executableDescent fs (LocalSearch.natCost δ (Finset.univ.image loc)) 5
        (fuelPoly.eval (pack (fun i j=>(δ (loc j) i:ℚ)) fs r).length) (fs.take r).toFinset).image original) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryLocalAnchor

end OAI
end
