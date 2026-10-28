-- Prove2me | Theorems.Thm_OAI_UniqueGamesTheorem_Inverse_KMSAnalyticHybridEnergy_uniformMixedBound_of_affineDensityBound
-- name    : OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.uniformMixedBound_of_affineDensityBound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:44:57.122119+00:00
-- url     : https://prove2.me/theorems/4f55cb62-55bb-47c5-a207-96d36ca88df7
-- title:
--   OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.uniformMixedBound_of_affineDensityBound: intermediate lemma from OpenAI, The Unique Games Theorem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniqueGamesTheorem.theorem11`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Unique Games Theorem*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.uniformMixedBound_of_affineDensityBound` of [lean/OAI/Computability/UniqueGames/Inverse/KMSLowLevelLemmas.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/UniqueGames/Inverse/KMSLowLevelLemmas.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy`, with `open scoped BigOperators Classical`, `open UniqueGamesTheorem.Integration.BinaryLinear (F2)`, `open UniqueGamesTheorem.Inverse.KMSAnalytic`, `open UniqueGamesTheorem.Inverse.KMSFourthMoment`):
--
--   ```lean
--   theorem uniformMixedBound_of_affineDensityBound (r : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
--       (f : (E →ₗ[F2] F) → ℝ) (hf : KMSBasisInvariant.IsBasisInvariant f)
--       (hd : AffineDensityBound r ε f) :
--       UniformMixedBound r (mixedRankConstant r * ε) f
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniqueGamesTheorem.Inverse.KMSFourthMoment.mixedRankConstant` (definitions bundle `OAIQ086U002` of this split); `OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.UniformMixedBound`, `OAI.UniqueGamesTheorem.Inverse.KMSBasisInvariant.IsBasisInvariant` and `OAI.UniqueGamesTheorem.Inverse.KMSFourthMoment.AffineDensityBound` (definitions bundle `OAIQ086U009` of this split); `OAI.UniqueGamesTheorem.Integration.BinaryLinear.F2` (the published bundle `Def_UniqueGamesTheorem`).
--
--   **Used by.** The proof of `OAI.UniqueGamesTheorem.Inverse.ShortcodeTheorem.inversePrinciple` of this split imports it.
-- source:
--   OpenAI, The Unique Games Theorem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Unique-Games-Theorem-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/UniqueGames/Inverse/KMSLowLevelLemmas.lean (declaration OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.uniformMixedBound_of_affineDensityBound)

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_UniqueGamesTheorem
import Definitions.Def_OAIQ086U009

section

attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Inverse.KMSAnalytic
open UniqueGamesTheorem.Inverse.KMSFourthMoment

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
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end OAI
end
