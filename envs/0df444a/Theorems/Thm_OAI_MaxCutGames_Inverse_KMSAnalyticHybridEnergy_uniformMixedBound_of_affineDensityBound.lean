-- Prove2me | Theorems.Thm_OAI_MaxCutGames_Inverse_KMSAnalyticHybridEnergy_uniformMixedBound_of_affineDensityBound
-- name    : OAI.MaxCutGames.Inverse.KMSAnalyticHybridEnergy.uniformMixedBound_of_affineDensityBound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T17:44:22.589073+00:00
-- url     : https://prove2.me/theorems/dc7b8489-f8d6-4337-b36c-a93d57cdfaa7
-- title:
--   OAI.MaxCutGames.Inverse.KMSAnalyticHybridEnergy.uniformMixedBound_of_affineDensityBound: intermediate lemma from OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaxCutGames.Inverse.KMSAnalyticHybridEnergy.uniformMixedBound_of_affineDensityBound` of [lean/OAI/Computability/MaxCut/Games/KMSAnalyticRestrictionTransport.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Games/KMSAnalyticRestrictionTransport.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaxCutGames.Inverse.KMSAnalyticHybridEnergy`, with `open scoped BigOperators Classical`, `open MaxCutGames.Integration.BinaryLinear (F2)`, `open MaxCutGames.Inverse.KMSAnalytic`, `open MaxCutGames.Inverse.KMSFourthMoment`):
--
--   ```lean
--   theorem uniformMixedBound_of_affineDensityBound (r : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
--       (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
--       (hd : AffineDensityBound r ε f) :
--       UniformMixedBound r (mixedRankConstant r * ε) f
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaxCutGames.Integration.BinaryLinear.F2` (definitions bundle `OAIQ087A000` of this split); `OAI.MaxCutGames.Inverse.KMSFourthMoment.mixedRankConstant` (definitions bundle `OAIQ087A005` of this split); `OAI.MaxCutGames.Inverse.KMSAnalyticHybridEnergy.UniformMixedBound`, `OAI.MaxCutGames.Inverse.KMSBasisInvariant.IsBasisInvariant` and `OAI.MaxCutGames.Inverse.KMSFourthMoment.AffineDensityBound` (definitions bundle `OAIQ087A012` of this split).
--
--   **Used by.** The proof of `OAI.MaxCutGames.Inverse.KMSMomentTheorem.lifted_fourth_moment_bound` of this split imports it.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Games/KMSAnalyticRestrictionTransport.lean (declaration OAI.MaxCutGames.Inverse.KMSAnalyticHybridEnergy.uniformMixedBound_of_affineDensityBound)

import Mathlib
import Definitions.Def_OAIQ087A012

section

attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Inverse.KMSAnalytic
open MaxCutGames.Inverse.KMSFourthMoment

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
end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

end OAI
end
