-- Prove2me | Theorems.Thm_LindbladStructLearn_Mach_A1_S0_run
-- name    : LindbladStructLearn.Mach.A1.S0_run
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T02:44:13.10833+00:00
-- url     : https://prove2.me/theorems/27a0fcb6-7605-4719-ad6c-c992b4fea706
-- title:
--   Initialisation run
-- statement:
--   From the input configuration `alg1Input n M ε δ`, the learner `prog k` runs deterministically for exactly $71$ steps. It reaches the post-initialisation state `st0` with the program counter at $71$, the start of the sampling block.
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
theorem S0_run (k n M : ℕ) (ε δ : ℝ) :
    DetRun (prog k) 71 (alg1Input n M ε δ) (setpc (st0 k n M ε δ) 71) := by sorry
end LindbladStructLearn.Mach.A1
