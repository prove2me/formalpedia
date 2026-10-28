-- Prove2me | Theorems.Thm_OAI_ScalarConductivity_endingJoin_constitution_ae
-- name    : OAI.ScalarConductivity.endingJoin_constitution_ae
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T21:48:07.679847+00:00
-- url     : https://prove2.me/theorems/e334fb64-6852-4ab3-b468-9b42dcce06c1
-- title:
--   OAI.ScalarConductivity.endingJoin_constitution_ae: intermediate lemma from OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ScalarConductivity.endingJoin_constitution_ae` of [lean/OAI/Analysis/Conductivity/Scalarization/EndingJoinConstitution.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Scalarization/EndingJoinConstitution.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ScalarConductivity`, with `open Set Filter Topology Real MeasureTheory Matrix`):
--
--   ```lean
--   lemma endingJoin_constitution_ae {D : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
--       {lam k J L K : ℝ} (hk : 0<k) (hJ : 0<J) (hL : 1≤L) (hK : 0<K)
--       (hu : ∀ x : Coord3,4≤x 0 → u x=![x 0,exp (-lam*x 0)*cos (k*x 2)]) :
--       ∀ᵐ x : Coord3,∀ j : Fin 2,
--         (endingJoinTensor D lam k J L K x*gradientColumns
--           (fderiv ℝ (matchedEndingPair u lam k J L K) x)).col j=joinedFlux D u lam k J L K j x
--   ```
--
--   **Definitions.** The statement is written with `OAI.ScalarConductivity.Coord3`, `OAI.ScalarConductivity.Mat3` and `OAI.ScalarConductivity.gradientColumns` (definitions bundle `OAIQ059C000` of this split); `OAI.ScalarConductivity.endingJoinTensor`, `OAI.ScalarConductivity.joinedFlux` and `OAI.ScalarConductivity.matchedEndingPair` (definitions bundle `OAIQ059C007` of this split).
--
--   **Used by.** The proofs of `OAI.ScalarConductivity.matchedEnding_weak_equation` and `OAI.ScalarConductivity.physicalFiniteEndingData_nonempty` of this split import it.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Scalarization/EndingJoinConstitution.lean (declaration OAI.ScalarConductivity.endingJoin_constitution_ae)

import Mathlib
import Definitions.Def_OAIQ059C007

section

attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma endingJoin_constitution_ae {D : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    {lam k J L K : ℝ} (hk : 0<k) (hJ : 0<J) (hL : 1≤L) (hK : 0<K)
    (hu : ∀ x : Coord3,4≤x 0 → u x=![x 0,exp (-lam*x 0)*cos (k*x 2)]) :
    ∀ᵐ x : Coord3,∀ j : Fin 2,
      (endingJoinTensor D lam k J L K x*gradientColumns
        (fderiv ℝ (matchedEndingPair u lam k J L K) x)).col j=joinedFlux D u lam k J L K j x := by
  sorry

end ScalarConductivity

end
end

end OAI
end
