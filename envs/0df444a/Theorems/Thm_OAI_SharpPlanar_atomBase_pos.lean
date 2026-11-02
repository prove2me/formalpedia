-- Prove2me | Theorems.Thm_OAI_SharpPlanar_atomBase_pos
-- name    : OAI.SharpPlanar.atomBase_pos
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T14:22:34.857741+00:00
-- url     : https://prove2.me/theorems/f13fc269-4978-4c6b-a046-7aa91982b21d
-- title:
--   OAI.SharpPlanar.atomBase_pos: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.atomBase_pos` of [lean/OAI/Analysis/PlanarPacking/AtomTail.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/AtomTail.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open IntegerBasis`):
--
--   ```lean
--   lemma atomBase_pos (j : Fin 7) : 0<atomBase j
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.atomBase` (definitions bundle `OAIQ098D002` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.atomBase_contains`, `OAI.SharpPlanar.atomIntCap_nonneg`, `OAI.SharpPlanar.error_large_cap`, `OAI.SharpPlanar.error_zero_cap`, `OAI.SharpPlanar.exact_head_lower`, `OAI.SharpPlanar.halfSign_1_N0_right`, `OAI.SharpPlanar.halfSign_1_N1_left`, `OAI.SharpPlanar.halfSign_1_N1_right` and `OAI.SharpPlanar.tailErrorJet_bound` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/AtomTail.lean (declaration OAI.SharpPlanar.atomBase_pos)

import Mathlib
import Definitions.Def_OAIQ098D002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerBasis
lemma atomBase_pos (j : Fin 7) : 0<atomBase j := by
  sorry
end SharpPlanar

end OAI
end
