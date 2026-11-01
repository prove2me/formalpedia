-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_contractionForm_haar_s50
-- name    : OAI.Laughlin.Fock.contractionForm_haar_s50
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T20:49:36.437206+00:00
-- url     : https://prove2.me/theorems/5fa19b12-2b07-4617-b07b-260bf8541593
-- title:
--   OAI.Laughlin.Fock.contractionForm_haar_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.contractionForm_haar` of [lean/OAI/Analysis/Laughlin/Fock/HaarQuadratic.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Fock/HaarQuadratic.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open Rotation MeasureTheory`, `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem contractionForm_haar_s50 {I : Type*} [Fintype I] [DecidableEq I]
--       (Q : ℕ) (ρ : SourceSU2 →* Matrix I I ℂ)
--       (hρ : ∀ g, ρ g⁻¹=(ρ g)ᴴ)
--       (hc : ∀ i j, Continuous (fun g => ρ g i j))
--       (minus : I → Module.End ℂ (Space Q))
--       (hm : ∀ g i x, minus i (exteriorRotation Q g x) =
--         ∑ j, ρ g i j • exteriorRotation Q g (minus j x))
--       (M : Matrix I I ℂ) (x : Space Q) :
--       (∫ g, contractionForm Q minus M (exteriorRotation Q g⁻¹ x) ∂sourceHaar) =
--         contractionForm Q minus (matrixIntegral sourceHaar (conjugateOrbit ρ M)) x
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Fock.contractionForm` and `OAI.Laughlin.Rotation.SourceSU2` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Rotation.conjugateOrbit` and `OAI.Laughlin.Rotation.matrixIntegral` (definitions bundle `OAIQ050L007` of this split); `OAI.Laughlin.Rotation.sourceHaar` and `OAI.Laughlin.Rotation.sourceSU2_measurableSpace` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Fock.exteriorRotation` (definitions bundle `OAIQ050L016` of this split); `OAI.Laughlin.Fock.Orbital` and `OAI.Laughlin.Fock.Space` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proofs of `OAI.Laughlin.Fock.physicalFourCopyEnd_cross_haar_s50`, `OAI.Laughlin.Fock.physical_family_spin_norm_haar_s50`, `OAI.Laughlin.Fock.physical_pair_norm_haar_real_s50`, `OAI.Laughlin.Fock.physical_threeBody_Fock_haar_real_s50`, `OAI.Laughlin.Fock.physical_twoBody_certificate_haar_s50` and `OAI.Laughlin.Fock.sourceA4Form_retained_s50` of this split import it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Fock/HaarQuadratic.lean (declaration OAI.Laughlin.Fock.contractionForm_haar)

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L016

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem contractionForm_haar_s50 {I : Type*} [Fintype I] [DecidableEq I]
    (Q : ℕ) (ρ : SourceSU2 →* Matrix I I ℂ)
    (hρ : ∀ g, ρ g⁻¹=(ρ g)ᴴ)
    (hc : ∀ i j, Continuous (fun g => ρ g i j))
    (minus : I → Module.End ℂ (Space Q))
    (hm : ∀ g i x, minus i (exteriorRotation Q g x) =
      ∑ j, ρ g i j • exteriorRotation Q g (minus j x))
    (M : Matrix I I ℂ) (x : Space Q) :
    (∫ g, contractionForm Q minus M (exteriorRotation Q g⁻¹ x) ∂sourceHaar) =
      contractionForm Q minus (matrixIntegral sourceHaar (conjugateOrbit ρ M)) x := by
  sorry

end Laughlin.Fock

end OAI
end
