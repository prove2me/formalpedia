-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_spectrumBox_mem_eu
-- name    : OAI.AtomicTriangular.FiniteCertificate.spectrumBox_mem_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T13:28:39.87897+00:00
-- url     : https://prove2.me/theorems/6a34a14d-3cdb-41c7-b1c9-11e9bc61834e
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.spectrumBox_mem_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.spectrumBox_mem` of [lean/OAI/Analysis/Triangular/Taylor/TaylorSpectrum.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorSpectrum.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval Complex`):
--
--   ```lean
--   lemma spectrumBox_mem_eu (side q : Fin 2) (j : Fin 31) (r : Fin 8) :
--       (spectrumBox side q j r).Mem (finiteSpectrum side q j r)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Interval.CI.Mem` (definitions bundle `OAIQ334E000` of this split); `OAI.AtomicTriangular.Construction.finiteSpectrum` (definitions bundle `OAIQ334E011` of this split); `OAI.AtomicTriangular.FiniteCertificate.spectrumBox` (definitions bundle `OAIQ334E022` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.FiniteCertificate.spectrumTable_mem_eu` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorSpectrum.lean (declaration OAI.AtomicTriangular.FiniteCertificate.spectrumBox_mem)

import Mathlib
import Definitions.Def_OAIQ334E022

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
lemma spectrumBox_mem_eu (side q : Fin 2) (j : Fin 31) (r : Fin 8) :
    (spectrumBox side q j r).Mem (finiteSpectrum side q j r) := by
  sorry

end AtomicTriangular.FiniteCertificate
end

end OAI
end
