-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_OperationalConstants_bad_stationary_array_law
-- name    : OAI.DirectionalTransience.OperationalConstants.bad_stationary_array_law
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:57:42.753234+00:00
-- url     : https://prove2.me/theorems/3a4cfba7-e5c4-432a-9a9e-92097bb24342
-- title:
--   OAI.DirectionalTransience.OperationalConstants.bad_stationary_array_law: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.OperationalConstants.bad_stationary_array_law` of [lean/OAI/Probability/Ballisticity/Stationary/StationaryArrayLaw.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Stationary/StationaryArrayLaw.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience.OperationalConstants`, with `open MeasureTheory ProbabilityTheory InformationTheory Filter`, `open scoped ENNReal NNReal Classical Topology BigOperators`):
--
--   ```lean
--   theorem bad_stationary_array_law (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
--       (hD : 0≤D) (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop)
--       (hN : ∀ n, C.sfloor≤(Ns n:ℝ)) (hlarge : ∀ n, 32*C.b≤(1/2:ℝ)*Real.log (Ns n:ℝ))
--       (hmass : ∀ n, (Ns n:ℝ)^(-D)≤(environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2))) :
--       Nonempty (StationaryArrayLaw ν e)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.OperationalConstants` (definitions bundle `OAIQ242Bal002` of this split); `OAI.DirectionalTransience.badCrossingEvent` (definitions bundle `OAIQ242Bal003` of this split); `OAI.DirectionalTransience.StationaryArrayLaw` (definitions bundle `OAIQ242Bal005` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.Environment`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Row` and `OAI.DirectionalTransience.environmentLaw` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proofs of `OAI.DirectionalTransience.crossing_failure_rapidDecay` and `OAI.DirectionalTransience.stripTime_rapidDecay` of this split import it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Stationary/StationaryArrayLaw.lean (declaration OAI.DirectionalTransience.OperationalConstants.bad_stationary_array_law)

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal005

section

attribute [-instance] _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e f : Direction d} {D : ℝ}

theorem bad_stationary_array_law (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (hD : 0≤D) (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop)
    (hN : ∀ n, C.sfloor≤(Ns n:ℝ)) (hlarge : ∀ n, 32*C.b≤(1/2:ℝ)*Real.log (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D)≤(environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2))) :
    Nonempty (StationaryArrayLaw ν e) := by
  sorry

end OperationalConstants
end DirectionalTransience

end

end OAI
end
