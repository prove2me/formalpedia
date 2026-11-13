-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderBox_mem_eu
-- name    : OAI.AtomicTriangular.FiniteCertificate.remainderBox_mem_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T21:01:55.165395+00:00
-- url     : https://prove2.me/theorems/cb9074fb-4982-464b-a3c7-8529cf35908a
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.remainderBox_mem_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.remainderBox_mem` of [lean/OAI/Analysis/Triangular/Signs/RemainderBoxes.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderBoxes.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open AtomicTriangular.FiniteCertificate`, `open Construction AtomicTriangular.Interval Complex`):
--
--   ```lean
--   lemma remainderBox_mem_eu (q br : Fin 2) (n : Fin 7) (j : Fin 31) {dnorm : RI}
--       (hd : dnorm.Mem ‖taylorPhase q br (frequency j)‖)
--       (hp : (remainderExpInput q br n j).normSq.hi ≤ scale*1024^2)
--       (hden : 0<((RI.point 1).sub (((nearRadiusBox n).mul dnorm).divNat 24)).lo) :
--       (remainderBox q br n j dnorm).Mem
--         (remainderWave q br (nearNode n) (nearRadius n) (frequency j))
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.frequency`, `OAI.AtomicTriangular.Interval.RI`, `OAI.AtomicTriangular.Interval.scale`, `OAI.AtomicTriangular.Interval.CI.normSq`, `OAI.AtomicTriangular.Interval.RI.Mem`, `OAI.AtomicTriangular.Interval.RI.divNat`, `OAI.AtomicTriangular.Interval.RI.mul`, `OAI.AtomicTriangular.Interval.RI.point` and `OAI.AtomicTriangular.Interval.RI.sub` (definitions bundle `OAIQ334E000` of this split); `OAI.AtomicTriangular.Construction.taylorPhase` (definitions bundle `OAIQ334E009` of this split); `OAI.AtomicTriangular.Construction.nearRadius`, `OAI.AtomicTriangular.Construction.remainderWave` and `OAI.AtomicTriangular.FiniteCertificate.nearNode` (definitions bundle `OAIQ334E011` of this split); `OAI.AtomicTriangular.FiniteCertificate.nearRadiusBox` (definitions bundle `OAIQ334E020` of this split); `OAI.AtomicTriangular.FiniteCertificate.remainderBox` and `OAI.AtomicTriangular.FiniteCertificate.remainderExpInput` (definitions bundle `OAIQ334E021` of this split).
--
--   **Used by.** The proofs of `OAI.AtomicTriangular.FiniteCertificate.remainderColumns1_0_bound_eu`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns2_0_bound_eu`, `OAI.AtomicTriangular.FiniteCertificate.remainderConst0_1_bound_eu`, `OAI.AtomicTriangular.FiniteCertificate.remainderConst5_0_bound_eu`, `OAI.AtomicTriangular.FiniteCertificate.remainderData0_00_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.remainderData0_10_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.remainderData0_11_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.remainderData2_00_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.remainderTable1_eu` and `OAI.AtomicTriangular.FiniteCertificate.remainderTable2_eu` of this split import it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderBoxes.lean (declaration OAI.AtomicTriangular.FiniteCertificate.remainderBox_mem)

import Mathlib
import Definitions.Def_OAIQ334E021

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open AtomicTriangular.FiniteCertificate
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderBox_mem_eu (q br : Fin 2) (n : Fin 7) (j : Fin 31) {dnorm : RI}
    (hd : dnorm.Mem ‖taylorPhase q br (frequency j)‖)
    (hp : (remainderExpInput q br n j).normSq.hi ≤ scale*1024^2)
    (hden : 0<((RI.point 1).sub (((nearRadiusBox n).mul dnorm).divNat 24)).lo) :
    (remainderBox q br n j dnorm).Mem
      (remainderWave q br (nearNode n) (nearRadius n) (frequency j)) := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
