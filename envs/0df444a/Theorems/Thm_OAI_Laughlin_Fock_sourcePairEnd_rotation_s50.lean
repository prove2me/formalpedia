-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_sourcePairEnd_rotation_s50
-- name    : OAI.Laughlin.Fock.sourcePairEnd_rotation_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:53:56.559434+00:00
-- url     : https://prove2.me/theorems/cdc7c2ee-6b0e-48ac-8ddd-cb8d3f329f2d
-- title:
--   OAI.Laughlin.Fock.sourcePairEnd_rotation_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.sourcePairEnd_rotation` of [lean/OAI/Analysis/Laughlin/Pair/FockCovariance.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Pair/FockCovariance.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open Rotation`, `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem sourcePairEnd_rotation_s50 (Q : ℕ) (hQ : 0 < Q) (g : SourceSU2)
--       (p : Fin (2*Q-2+1)) (x : Space Q) :
--       sourcePairEnd Q p.val (exteriorRotation Q g x) =
--         ∑ q : Fin (2*Q-2+1), sourceSpinRepresentation (2*Q-2) g p q •
--           exteriorRotation Q g (sourcePairEnd Q q.val x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Rotation.SourceSU2` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Fock.sourcePairEnd` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Fock.exteriorRotation` and `OAI.Laughlin.Rotation.sourceSpinRepresentation` (definitions bundle `OAIQ050L016` of this split); `OAI.Laughlin.Fock.Orbital` and `OAI.Laughlin.Fock.Space` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proofs of `OAI.Laughlin.Fock.physical_pair_norm_haar_real_s50`, `OAI.Laughlin.Fock.physical_threeBody_Fock_haar_real_s50`, `OAI.Laughlin.Fock.physical_twoBody_certificate_haar_s50` and `OAI.Laughlin.Fock.sourceThreeHighestEnd_haar_s50` of this split import it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Pair/FockCovariance.lean (declaration OAI.Laughlin.Fock.sourcePairEnd_rotation)

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

theorem sourcePairEnd_rotation_s50 (Q : ℕ) (hQ : 0 < Q) (g : SourceSU2)
    (p : Fin (2*Q-2+1)) (x : Space Q) :
    sourcePairEnd Q p.val (exteriorRotation Q g x) =
      ∑ q : Fin (2*Q-2+1), sourceSpinRepresentation (2*Q-2) g p q •
        exteriorRotation Q g (sourcePairEnd Q q.val x) := by
  sorry

end Laughlin.Fock

end OAI
end
