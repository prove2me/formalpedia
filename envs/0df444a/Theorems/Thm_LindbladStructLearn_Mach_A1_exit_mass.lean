-- Prove2me | Theorems.Thm_LindbladStructLearn_Mach_A1_exit_mass
-- name    : LindbladStructLearn.Mach.A1.exit_mass
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T02:43:35.320776+00:00
-- url     : https://prove2.me/theorems/c93617e8-d637-5289-8978-2db9ca9e89c8
-- title:
--   Leaving the sampling loop (mass)
-- statement:
--   At the sampling-loop test (pc $71$) with no output and the round counter $p_3\ge M=p_1$, the program spends two steps (the exit jump and copying the output pointer $p_{12}:=p_4$). It reaches the record phase at pc $96$, so
--   $$\mathrm{mass}_{N+2}(s,E)=\mathrm{mass}_N(\mathrm{exitSt}\,s,E).$$
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
theorem exit_mass {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)} (k N : ℕ) (E : MState → Prop) (s : MState) (hout : s.output = none)
    (hle : s.core.ptrs 1 ≤ s.core.ptrs 3) :
    mass (prog k) n evo (N + 2) (setpc s 71) E = mass (prog k) n evo N (setpc (exitSt s) 96) E := by sorry
end LindbladStructLearn.Mach.A1
