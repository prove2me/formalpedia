-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_3_12_calc_x
-- name    : OAI.AtomicTriangular.FiniteCertificate.tw1_0_3_12_calc_x
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T06:46:23.141201+00:00
-- url     : https://prove2.me/theorems/9ab9bb07-31f5-4a6a-8ad0-9077eeb4dc59
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.tw1_0_3_12_calc_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.tw1_0_3_12_calc` of [lean/OAI/Analysis/Triangular/Taylor/TaylorWave103.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave103.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval Complex`):
--
--   ```lean
--   lemma tw1_0_3_12_calc_x (j : Fin 31) : taylorWaveBox 1 0 3 12 j = tw1_0_3_12 j
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Interval.CI` (definitions bundle `OAIQ257X000` of this split); `OAI.AtomicTriangular.FiniteCertificate.tw1_0_3_12` (definitions bundle `OAIQ257X015` of this split); `OAI.AtomicTriangular.FiniteCertificate.taylorWaveBox` (definitions bundle `OAIQ257X025` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.FiniteCertificate.tw1_0_3_mem_x` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave103.lean (declaration OAI.AtomicTriangular.FiniteCertificate.tw1_0_3_12_calc)

import Mathlib
import Definitions.Def_OAIQ257X025

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_0_3_12_calc_x (j : Fin 31) : taylorWaveBox 1 0 3 12 j = tw1_0_3_12 j := by
  sorry

end AtomicTriangular.FiniteCertificate
end

end OAI
end
