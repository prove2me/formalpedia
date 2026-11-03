-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_exteriorFamily_contraction_rotation_s50
-- name    : OAI.Laughlin.Fock.exteriorFamily_contraction_rotation_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:49:53.886949+00:00
-- url     : https://prove2.me/theorems/a815797d-51ec-4098-b750-47de8d80995f
-- title:
--   OAI.Laughlin.Fock.exteriorFamily_contraction_rotation_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.exteriorFamily_contraction_rotation` of [lean/OAI/Analysis/Laughlin/Exterior/FamilyCovariance.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Exterior/FamilyCovariance.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open Rotation`, `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem exteriorFamily_contraction_rotation_s50 {I : Type*} [Fintype I] [DecidableEq I]
--       (Q : ℕ) (ρ : SourceSU2 →* Matrix I I ℂ)
--       (hρ : ∀ g, ρ g⁻¹=(ρ g)ᴴ)
--       (v : I → Space Q) (minus : I → Module.End ℂ (Space Q))
--       (ha : ∀ i x y, occupationInner Q (v i*x) y = occupationInner Q x (minus i y))
--       (hv : ∀ g i, exteriorRotation Q g (v i) = ∑ j, ρ g j i • v j)
--       (g : SourceSU2) (i : I) (x : Space Q) :
--       minus i (exteriorRotation Q g x) = ∑ j, ρ g i j • exteriorRotation Q g (minus j x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Fock.occupationInner` and `OAI.Laughlin.Rotation.SourceSU2` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Fock.exteriorRotation` (definitions bundle `OAIQ050L016` of this split); `OAI.Laughlin.Fock.Orbital` and `OAI.Laughlin.Fock.Space` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proofs of `OAI.Laughlin.Fock.sourceFourFamilyEnd_rotation_s50` and `OAI.Laughlin.Fock.sourcePairEnd_rotation_s50` of this split import it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Exterior/FamilyCovariance.lean (declaration OAI.Laughlin.Fock.exteriorFamily_contraction_rotation)

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
open Rotation
open scoped BigOperators Matrix

theorem exteriorFamily_contraction_rotation_s50 {I : Type*} [Fintype I] [DecidableEq I]
    (Q : ℕ) (ρ : SourceSU2 →* Matrix I I ℂ)
    (hρ : ∀ g, ρ g⁻¹=(ρ g)ᴴ)
    (v : I → Space Q) (minus : I → Module.End ℂ (Space Q))
    (ha : ∀ i x y, occupationInner Q (v i*x) y = occupationInner Q x (minus i y))
    (hv : ∀ g i, exteriorRotation Q g (v i) = ∑ j, ρ g j i • v j)
    (g : SourceSU2) (i : I) (x : Space Q) :
    minus i (exteriorRotation Q g x) = ∑ j, ρ g i j • exteriorRotation Q g (minus j x) := by
  sorry

end Laughlin.Fock

end OAI
end
