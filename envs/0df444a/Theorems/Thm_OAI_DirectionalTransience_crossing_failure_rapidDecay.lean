-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_crossing_failure_rapidDecay
-- name    : OAI.DirectionalTransience.crossing_failure_rapidDecay
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:45:42.503899+00:00
-- url     : https://prove2.me/theorems/c215da5f-a6af-4b9c-9462-9667965b532f
-- title:
--   OAI.DirectionalTransience.crossing_failure_rapidDecay: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.crossing_failure_rapidDecay` of [lean/OAI/Probability/Ballisticity/Crossings/CrossingSurplus.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Crossings/CrossingSurplus.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal Classical Topology BigOperators`):
--
--   ```lean
--   lemma crossing_failure_rapidDecay {d : ℕ} (hd : 2≤d) (ν : Measure (Row d))
--       [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e : Direction d)
--       (htrans : DirectionallyTransient ν (realPosition (step e))) :
--       RapidDecay (fun N => (annealedLaw ν).real
--         (Cross (realPosition (step e)) 0 N \ NoDrop (realPosition (step e)) 0))
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.Cross` and `OAI.DirectionalTransience.NoDrop` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.RapidDecay` (definitions bundle `OAIQ242Bal001` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.DirectionallyTransient`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Path`, `OAI.DirectionalTransience.Row`, `OAI.DirectionalTransience.UniformElliptic`, `OAI.DirectionalTransience.annealedLaw`, `OAI.DirectionalTransience.realPosition` and `OAI.DirectionalTransience.step` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity` of this split imports it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Crossings/CrossingSurplus.lean (declaration OAI.DirectionalTransience.crossing_failure_rapidDecay)

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal000
import Definitions.Def_OAIQ242Bal001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma crossing_failure_rapidDecay {d : ℕ} (hd : 2≤d) (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    RapidDecay (fun N => (annealedLaw ν).real
      (Cross (realPosition (step e)) 0 N \ NoDrop (realPosition (step e)) 0)) := by
  sorry

end DirectionalTransience

end

end OAI
end
