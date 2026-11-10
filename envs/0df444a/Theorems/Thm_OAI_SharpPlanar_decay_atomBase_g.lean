-- Prove2me | Theorems.Thm_OAI_SharpPlanar_decay_atomBase_g
-- name    : OAI.SharpPlanar.decay_atomBase_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T20:54:02.463496+00:00
-- url     : https://prove2.me/theorems/4508e082-ad1a-4690-ab1c-8976a9b6ea8b
-- title:
--   OAI.SharpPlanar.decay_atomBase_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.decay_atomBase` of [lean/OAI/Analysis/PlanarPacking/AtomTail.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/AtomTail.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open IntegerBasis`):
--
--   ```lean
--   lemma decay_atomBase_g (j : Fin 7) (n : ℕ) :
--       Real.exp (-Real.pi*dampingCap j*n) ≤ atomBase j^n
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.atomBase` (definitions bundle `OAIQ098G1643` of this split); `OAI.SharpPlanar.dampingCap` (definitions bundle `OAIQ098G362` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.atomicEnvelope_le_rat_g`, `OAI.SharpPlanar.error_large_cap_g`, `OAI.SharpPlanar.error_one_cap_g`, `OAI.SharpPlanar.error_two_cap_g`, `OAI.SharpPlanar.error_zero_cap_g`, `OAI.SharpPlanar.exact_head_lower_g` and `OAI.SharpPlanar.tail_second_bound_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/AtomTail.lean (declaration OAI.SharpPlanar.decay_atomBase)

import Mathlib
import Definitions.Def_OAIQ098G362
import Definitions.Def_OAIQ098G1643

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerBasis
lemma decay_atomBase_g (j : Fin 7) (n : ℕ) :
    Real.exp (-Real.pi*dampingCap j*n) ≤ atomBase j^n := by
  sorry
end SharpPlanar

end OAI
end
