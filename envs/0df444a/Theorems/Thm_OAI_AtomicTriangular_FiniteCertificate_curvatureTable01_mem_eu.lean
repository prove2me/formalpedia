-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureTable01_mem_eu
-- name    : OAI.AtomicTriangular.FiniteCertificate.curvatureTable01_mem_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T13:27:09.399202+00:00
-- url     : https://prove2.me/theorems/63d258d1-f2e1-48bb-8124-36035c2f4939
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.curvatureTable01_mem_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.curvatureTable01_mem` of [lean/OAI/Analysis/Triangular/Taylor/CurvatureData01.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/CurvatureData01.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval Complex`):
--
--   ```lean
--   lemma curvatureTable01_mem_eu (i : Fin 5) (j : Fin 31) : (curvatureTable01 i j).Mem (curvatureWave 0 1 (curvaturePoint i) (frequency j))
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.frequency` and `OAI.AtomicTriangular.Interval.RI.Mem` (definitions bundle `OAIQ334E000` of this split); `OAI.AtomicTriangular.Construction.curvaturePoint` and `OAI.AtomicTriangular.Construction.curvatureWave` (definitions bundle `OAIQ334E011` of this split); `OAI.AtomicTriangular.FiniteCertificate.curvatureTable01` (definitions bundle `OAIQ334E020` of this split).
--
--   **Used by.** The proofs of `OAI.AtomicTriangular.Construction.actualJ0_curvature_eu` and `OAI.AtomicTriangular.Construction.tailCurvatureCap_sum_eu` of this split import it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/CurvatureData01.lean (declaration OAI.AtomicTriangular.FiniteCertificate.curvatureTable01_mem)

import Mathlib
import Definitions.Def_OAIQ334E011
import Definitions.Def_OAIQ334E020

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
lemma curvatureTable01_mem_eu (i : Fin 5) (j : Fin 31) : (curvatureTable01 i j).Mem (curvatureWave 0 1 (curvaturePoint i) (frequency j)) := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
