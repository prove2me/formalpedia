-- Prove2me | Theorems.Thm_OAI_SharpPlanar_Q_as_table_e
-- name    : OAI.SharpPlanar.Q_as_table_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T05:53:32.664085+00:00
-- url     : https://prove2.me/theorems/7d971817-9eb4-4b07-9554-f4ac4b568bce
-- title:
--   OAI.SharpPlanar.Q_as_table_e: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.Q_as_table` of [lean/OAI/Analysis/PlanarPacking/Nodes.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Nodes.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`):
--
--   ```lean
--   lemma Q_as_table_e (n : ℕ) : Q n =
--       (Real.pi/6)^2 * ∏ a ∈ residues.erase (n % 12),
--         (2 - 2*(cosTable (n%12)*cosTable a + sinTable (n%12)*sinTable a))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.residues` (definitions bundle `OAIQ098E000` of this split); `OAI.SharpPlanar.Q` (definitions bundle `OAIQ098E001` of this split); `OAI.SharpPlanar.cosTable` and `OAI.SharpPlanar.sinTable` (definitions bundle `OAIQ098E018` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Q_0_e`, `OAI.SharpPlanar.Q_1_e`, `OAI.SharpPlanar.Q_3_e`, `OAI.SharpPlanar.Q_4_e`, `OAI.SharpPlanar.Q_7_e` and `OAI.SharpPlanar.Q_9_e` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Nodes.lean (declaration OAI.SharpPlanar.Q_as_table)

import Mathlib
import Definitions.Def_OAIQ098E018

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar

lemma Q_as_table_e (n : ℕ) : Q n =
    (Real.pi/6)^2 * ∏ a ∈ residues.erase (n % 12),
      (2 - 2*(cosTable (n%12)*cosTable a + sinTable (n%12)*sinTable a)) := by
  sorry

end SharpPlanar

end OAI
end
