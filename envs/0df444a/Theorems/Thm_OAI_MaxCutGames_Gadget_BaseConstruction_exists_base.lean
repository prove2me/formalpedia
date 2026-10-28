-- Prove2me | Theorems.Thm_OAI_MaxCutGames_Gadget_BaseConstruction_exists_base
-- name    : OAI.MaxCutGames.Gadget.BaseConstruction.exists_base
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T17:46:02.995838+00:00
-- url     : https://prove2.me/theorems/a0bab25e-8528-4117-b5c8-7b47aa1103a0
-- title:
--   OAI.MaxCutGames.Gadget.BaseConstruction.exists_base: intermediate lemma from OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaxCutGames.Gadget.BaseConstruction.exists_base` of [lean/OAI/Computability/MaxCut/Games/FiniteFieldChoice.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Games/FiniteFieldChoice.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaxCutGames.Gadget.BaseConstruction`, with `open Quadratic QuadraticStageNoise Harmonic Parameters`, `open scoped Classical`):
--
--   ```lean
--   theorem exists_base (p : ℚ) (hp : 0 < p) :
--       ∃ d : ℕ, 0 < d ∧ ∃ n : ℕ,
--         StageNoiseRecurrence.error (quotientStage (F := BinaryField d) n) ≤ p ∧
--         ∀ (E : Type) [AddCommGroup E] [Module (ZMod 2) E]
--           (T : (quotientStage (F := BinaryField d) n).Input →ₗ[ZMod 2] E),
--           Function.Injective (T.comp (quotientStage (F := BinaryField d) n).embed) →
--           (1 / 4 : ℚ) ≤ StageNoiseRecurrence.average (fun t =>
--             if T ((quotientStage (F := BinaryField d) n).noise t) ≠ 0 then 1 else 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaxCutGames.Quadratic.Vec` and `OAI.MaxCutGames.Gadget.Stage` (definitions bundle `OAIQ087A004` of this split); `OAI.MaxCutGames.Quadratic.BinaryField`, `OAI.MaxCutGames.Quadratic.binaryFieldFintype` and `OAI.MaxCutGames.Gadget.StageNoiseRecurrence.average` (definitions bundle `OAIQ087A005` of this split); `OAI.MaxCutGames.Gadget.QuadraticStageNoise.quotientStage` and `OAI.MaxCutGames.Gadget.StageNoiseRecurrence.error` (definitions bundle `OAIQ087A012` of this split).
--
--   **Used by.** The proof of `OAI.MaxCutGames.theorem11` of this split imports it.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Games/FiniteFieldChoice.lean (declaration OAI.MaxCutGames.Gadget.BaseConstruction.exists_base)

import Mathlib
import Definitions.Def_OAIQ087A012

section

attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Gadget.BaseConstruction

open Quadratic QuadraticStageNoise Harmonic Parameters
open scoped Classical

noncomputable section

variable {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

theorem exists_base (p : ℚ) (hp : 0 < p) :
    ∃ d : ℕ, 0 < d ∧ ∃ n : ℕ,
      StageNoiseRecurrence.error (quotientStage (F := BinaryField d) n) ≤ p ∧
      ∀ (E : Type) [AddCommGroup E] [Module (ZMod 2) E]
        (T : (quotientStage (F := BinaryField d) n).Input →ₗ[ZMod 2] E),
        Function.Injective (T.comp (quotientStage (F := BinaryField d) n).embed) →
        (1 / 4 : ℚ) ≤ StageNoiseRecurrence.average (fun t =>
          if T ((quotientStage (F := BinaryField d) n).noise t) ≠ 0 then 1 else 0) := by
  sorry

end

end MaxCutGames.Gadget.BaseConstruction

end OAI
end
