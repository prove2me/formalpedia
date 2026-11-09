-- Prove2me | Theorems.Thm_OAI_SharpPlanar_directEnvelope_le_rat_g
-- name    : OAI.SharpPlanar.directEnvelope_le_rat_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T05:35:39.137252+00:00
-- url     : https://prove2.me/theorems/b2212677-e0f3-4a27-bce5-dfa47a855ac9
-- title:
--   OAI.SharpPlanar.directEnvelope_le_rat_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.directEnvelope_le_rat` of [lean/OAI/Analysis/PlanarPacking/RationalBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/RationalBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open IntegerBasis`, `open scoped BigOperators`):
--
--   ```lean
--   lemma directEnvelope_le_rat_g (ell : ℕ) : directEnvelope ell ≤ directRational ell
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.directEnvelope` (definitions bundle `OAIQ098G1675` of this split); `OAI.SharpPlanar.directRational` (definitions bundle `OAIQ098G1676` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.error_large_cap_g`, `OAI.SharpPlanar.error_one_cap_g`, `OAI.SharpPlanar.error_two_cap_g`, `OAI.SharpPlanar.error_zero_cap_g`, `OAI.SharpPlanar.table_jet_sharp_g` and `OAI.SharpPlanar.tail_second_bound_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/RationalBounds.lean (declaration OAI.SharpPlanar.directEnvelope_le_rat)

import Mathlib
import Definitions.Def_OAIQ098G1675
import Definitions.Def_OAIQ098G1676

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
lemma directEnvelope_le_rat_g (ell : ℕ) : directEnvelope ell ≤ directRational ell := by
  sorry
end SharpPlanar

end OAI
end
