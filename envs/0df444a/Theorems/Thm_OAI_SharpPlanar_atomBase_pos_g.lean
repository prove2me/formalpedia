-- Prove2me | Theorems.Thm_OAI_SharpPlanar_atomBase_pos_g
-- name    : OAI.SharpPlanar.atomBase_pos_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T16:36:07.735036+00:00
-- url     : https://prove2.me/theorems/3e110481-b2f5-4930-8aa7-4decc39b3ce5
-- title:
--   OAI.SharpPlanar.atomBase_pos_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.atomBase_pos` of [lean/OAI/Analysis/PlanarPacking/AtomTail.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/AtomTail.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`):
--
--   ```lean
--   lemma atomBase_pos_g (j : Fin 7) : 0<atomBase j
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.atomBase` (definitions bundle `OAIQ098G1643` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.atomBase_contains_g`, `OAI.SharpPlanar.atomicEnvelope_le_rat_g`, `OAI.SharpPlanar.error_large_cap_g`, `OAI.SharpPlanar.error_one_cap_g`, `OAI.SharpPlanar.error_two_cap_g`, `OAI.SharpPlanar.error_zero_cap_g`, `OAI.SharpPlanar.exact_head_lower_g` and `OAI.SharpPlanar.tail_second_bound_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/AtomTail.lean (declaration OAI.SharpPlanar.atomBase_pos)

import Mathlib
import Definitions.Def_OAIQ098G1643

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma atomBase_pos_g (j : Fin 7) : 0<atomBase j := by
  sorry
end SharpPlanar

end OAI
end
