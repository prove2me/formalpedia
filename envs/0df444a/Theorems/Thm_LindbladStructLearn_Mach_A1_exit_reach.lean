-- Prove2me | Theorems.Thm_LindbladStructLearn_Mach_A1_exit_reach
-- name    : LindbladStructLearn.Mach.A1.exit_reach
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T02:44:02.135226+00:00
-- url     : https://prove2.me/theorems/5ec5cbf5-5d6f-5f9f-9a09-1f761f44765e
-- title:
--   Leaving the sampling loop (reach)
-- statement:
--   At the sampling-loop test (pc $71$) with no output and $p_1\le p_3$, a configuration is reachable from $s$ in $N+2$ steps if and only if it is reachable in $N$ steps from the record-phase entry state `exitSt s` at pc $96$.
--
--   **Formalization Note** This is an auxiliary verification lemma for the learner program `prog k` defined in `Definitions.Def_LindbladStructLearn_Alg1Learner` (the witness for Lemma 2.10). States are learner-machine configurations `MState`; `ptrs`, `regs`, `intMem`, `core.mem` are its pointer registers, real registers, integer memory and real memory.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Algorithm 1 (p.17) and Lemma 2.10 (p.18). Auxiliary lemma in the verification of the learner program `prog k` for Lemma 2.10.

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model
import Definitions.Def_LindbladStructLearn_Admissible
import Definitions.Def_LindbladStructLearn_Reach
import Definitions.Def_LindbladStructLearn_mass
import Definitions.Def_LindbladStructLearn_Halted
import Definitions.Def_LindbladStructLearn_decode
import Definitions.Def_LindbladStructLearn_alg1Input
import Definitions.Def_LindbladStructLearn_IsChannel
import Definitions.Def_LindbladStructLearn_locFourier
import Definitions.Def_LindbladStructLearn_pairSupport
import Definitions.Def_LindbladStructLearn_alg1Sample
import Definitions.Def_LindbladStructLearn_Alg1Learner

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth
theorem exit_reach {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)} (k N : ℕ) (x : MState) (s : MState) (hout : s.output = none)
    (hle : s.core.ptrs 1 ≤ s.core.ptrs 3) :
    Reach (prog k) n evo (N + 2) (setpc s 71) x ↔ Reach (prog k) n evo N (setpc (exitSt s) 96) x := by sorry
end LindbladStructLearn.Mach.A1
