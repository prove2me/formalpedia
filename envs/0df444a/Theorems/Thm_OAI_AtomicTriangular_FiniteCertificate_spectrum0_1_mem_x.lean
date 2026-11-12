-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_spectrum0_1_mem_x
-- name    : OAI.AtomicTriangular.FiniteCertificate.spectrum0_1_mem_x
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T04:37:05.694906+00:00
-- url     : https://prove2.me/theorems/c94f3cb3-855a-4331-b887-c331175ca614
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.spectrum0_1_mem_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.spectrum0_1_mem` of [lean/OAI/Analysis/Triangular/Taylor/TaylorSpectrum.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorSpectrum.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval Complex`):
--
--   ```lean
--   lemma spectrum0_1_mem_x (j : Fin 31) (r : Fin 8) : (spectrum0_1 j r).Mem (finiteSpectrum 0 1 j r)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Interval.CI.Mem` (definitions bundle `OAIQ257X000` of this split); `OAI.AtomicTriangular.Construction.finiteSpectrum` (definitions bundle `OAIQ257X011` of this split); `OAI.AtomicTriangular.FiniteCertificate.spectrum0_1` (definitions bundle `OAIQ257X020` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.FiniteCertificate.spectrumTable_mem_x` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorSpectrum.lean (declaration OAI.AtomicTriangular.FiniteCertificate.spectrum0_1_mem)

import Mathlib
import Definitions.Def_OAIQ257X011
import Definitions.Def_OAIQ257X020

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
lemma spectrum0_1_mem_x (j : Fin 31) (r : Fin 8) : (spectrum0_1 j r).Mem (finiteSpectrum 0 1 j r) := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
