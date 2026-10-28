-- Prove2me | Theorems.Thm_OAI_DFVSGames_Inverse_KMSAnalyticHybridEnergy_uniformMixedBound_of_affineDensityBound
-- name    : OAI.DFVSGames.Inverse.KMSAnalyticHybridEnergy.uniformMixedBound_of_affineDensityBound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T17:03:42.713775+00:00
-- url     : https://prove2.me/theorems/31d4f3f2-3e5d-431b-b971-56fce00b5223
-- title:
--   OAI.DFVSGames.Inverse.KMSAnalyticHybridEnergy.uniformMixedBound_of_affineDensityBound: intermediate lemma from OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DFVSGames.Inverse.KMSAnalyticHybridEnergy.uniformMixedBound_of_affineDensityBound` of [lean/OAI/Computability/DirectedFeedback/Games/KMSAnalyticHybridEnergyMixed.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/Games/KMSAnalyticHybridEnergyMixed.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DFVSGames.Inverse.KMSAnalyticHybridEnergy`, with `open scoped BigOperators Classical`, `open DFVSGames.Integration.BinaryLinear (F2)`, `open DFVSGames.Inverse.KMSAnalytic`, `open DFVSGames.Inverse.KMSFourthMoment`):
--
--   ```lean
--   theorem uniformMixedBound_of_affineDensityBound (r : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
--       (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
--       (hd : AffineDensityBound r ε f) :
--       UniformMixedBound r (mixedRankConstant r * ε) f
--   ```
--
--   **Definitions.** The statement is written with `OAI.DFVSGames.Integration.BinaryLinear.F2` (definitions bundle `OAIQ085D000` of this split); `OAI.DFVSGames.Inverse.KMSFourthMoment.mixedRankConstant` (definitions bundle `OAIQ085D003` of this split); `OAI.DFVSGames.Inverse.KMSBasisInvariant.IsBasisInvariant` (definitions bundle `OAIQ085D016` of this split); `OAI.DFVSGames.Inverse.KMSAnalyticHybridEnergy.UniformMixedBound` and `OAI.DFVSGames.Inverse.KMSFourthMoment.AffineDensityBound` (definitions bundle `OAIQ085D027` of this split).
--
--   **Used by.** The proofs of `OAI_DFVSGames_Inverse_KMSExpansion_kms_expansion` and `OAI.DFVSGames.Inverse.KMSMomentTheorem.lifted_fourth_moment_bound` of this split import it.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/Games/KMSAnalyticHybridEnergyMixed.lean (declaration OAI.DFVSGames.Inverse.KMSAnalyticHybridEnergy.uniformMixedBound_of_affineDensityBound)

import Mathlib
import Definitions.Def_OAIQ085D027

section

attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Inverse.KMSAnalytic
open DFVSGames.Inverse.KMSFourthMoment

universe u v w

attribute [local instance] mixedMapFintype

variable {E : Type u} {F : Type v}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F]

theorem uniformMixedBound_of_affineDensityBound (r : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
    (hd : AffineDensityBound r ε f) :
    UniformMixedBound r (mixedRankConstant r * ε) f := by
  sorry

end
end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end OAI
end
