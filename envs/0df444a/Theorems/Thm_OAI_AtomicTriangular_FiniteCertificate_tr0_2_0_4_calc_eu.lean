-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_2_0_4_calc_eu
-- name    : OAI.AtomicTriangular.FiniteCertificate.tr0_2_0_4_calc_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T13:37:48.786747+00:00
-- url     : https://prove2.me/theorems/1aec3496-d262-4b02-bd79-3c34a9d6c375
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.tr0_2_0_4_calc_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.tr0_2_0_4_calc` of [lean/OAI/Analysis/Triangular/Taylor/TaylorRows02.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows02.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval`):
--
--   ```lean
--   lemma tr0_2_0_4_calc_eu (r : Fin 8) : taylorRowBox 0 2 0 4 r = tr0_2_0_4 r
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Interval.RI` (definitions bundle `OAIQ334E000` of this split); `OAI.AtomicTriangular.FiniteCertificate.tr0_2_0_4` (definitions bundle `OAIQ334E013` of this split); `OAI.AtomicTriangular.FiniteCertificate.taylorRowBox` (definitions bundle `OAIQ334E023` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.FiniteCertificate.tr0_2_0_mem_eu` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows02.lean (declaration OAI.AtomicTriangular.FiniteCertificate.tr0_2_0_4_calc)

import Mathlib
import Definitions.Def_OAIQ334E023

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_2_0_4_calc_eu (r : Fin 8) : taylorRowBox 0 2 0 4 r = tr0_2_0_4 r := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
