-- Prove2me | Theorems.Thm_OAI_ScalarConductivity_matchedEnding_regularRegion_ae
-- name    : OAI.ScalarConductivity.matchedEnding_regularRegion_ae
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T21:58:50.227856+00:00
-- url     : https://prove2.me/theorems/93ef4ebd-fc8b-4b3b-a218-f7b168326d39
-- title:
--   OAI.ScalarConductivity.matchedEnding_regularRegion_ae: intermediate lemma from OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ScalarConductivity.matchedEnding_regularRegion_ae` of [lean/OAI/Analysis/Conductivity/Branching/MatchedEndingRegularity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Branching/MatchedEndingRegularity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ScalarConductivity`, with `open Set Filter Topology Real MeasureTheory Matrix`, `open scoped Matrix.Norms.Elementwise`):
--
--   ```lean
--   theorem matchedEnding_regularRegion_ae {D : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
--       (hD : ContDiff ℝ (↑(⊤:ℕ∞)) D) (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
--       (hDs : ∀ x,(D x).IsSymm) {s : Fin 3 → ℝ} {lam k J L K : ℝ}
--       (hk : 0<k) (hJ : 0<J) (hL : 0<L) (hK : 0<K)
--       (hum : ∀ x : Coord3,4≤x 0 → u x=![x 0,exp (-lam*x 0)*cos (k*x 2)])
--       (hDm : ∀ x : Coord3,x 0∈Icc (6:ℝ) 7 → D x=flatBackgroundTensor s)
--       (hur : ∀ᵐ x : Coord3,x 0∈Ioo 0 6 → LinearIndependent ℝ (gradientColumns (fderiv ℝ u x)).col)
--       {U : Set Coord3} (hU : IsOpen U) (hUpos : U⊆{x : Coord3 | 0<x 0}) :
--       ∀ᵐ x : Coord3,x∈U → x∈regularRegion (matchedEndingPair u lam k J L K)
--         (endingJoinSymmetricTensor D hDs lam k J L K) U
--   ```
--
--   **Definitions.** The statement is written with `OAI.ScalarConductivity.Coord3`, `OAI.ScalarConductivity.Mat3`, `OAI.ScalarConductivity.gradientColumns` and `OAI.ScalarConductivity.regularRegion` (definitions bundle `OAIQ059C000` of this split); `OAI.ScalarConductivity.flatBackgroundTensor` (definitions bundle `OAIQ059C003` of this split); `OAI.ScalarConductivity.endingJoinSymmetricTensor` and `OAI.ScalarConductivity.matchedEndingPair` (definitions bundle `OAIQ059C007` of this split).
--
--   **Used by.** The proof of `OAI.ScalarConductivity.physicalFiniteEndingData_nonempty` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Branching/MatchedEndingRegularity.lean (declaration OAI.ScalarConductivity.matchedEnding_regularRegion_ae)

import Mathlib
import Definitions.Def_OAIQ059C007

section

attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

theorem matchedEnding_regularRegion_ae {D : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    (hD : ContDiff ℝ (↑(⊤:ℕ∞)) D) (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hDs : ∀ x,(D x).IsSymm) {s : Fin 3 → ℝ} {lam k J L K : ℝ}
    (hk : 0<k) (hJ : 0<J) (hL : 0<L) (hK : 0<K)
    (hum : ∀ x : Coord3,4≤x 0 → u x=![x 0,exp (-lam*x 0)*cos (k*x 2)])
    (hDm : ∀ x : Coord3,x 0∈Icc (6:ℝ) 7 → D x=flatBackgroundTensor s)
    (hur : ∀ᵐ x : Coord3,x 0∈Ioo 0 6 → LinearIndependent ℝ (gradientColumns (fderiv ℝ u x)).col)
    {U : Set Coord3} (hU : IsOpen U) (hUpos : U⊆{x : Coord3 | 0<x 0}) :
    ∀ᵐ x : Coord3,x∈U → x∈regularRegion (matchedEndingPair u lam k J L K)
      (endingJoinSymmetricTensor D hDs lam k J L K) U := by
  sorry

end ScalarConductivity

end

end OAI
end
