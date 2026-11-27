-- Prove2me | Theorems.Thm_LindbladStructLearn_Mach_A1_st0_facts
-- name    : LindbladStructLearn.Mach.A1.st0_facts
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T02:44:08.766524+00:00
-- url     : https://prove2.me/theorems/a9b110a7-d070-4e3d-af77-2f38476a5616
-- title:
--   State after initialisation
-- statement:
--   Running the initialisation block `S0 k` on the input `alg1Input n M ε δ` gives a state with:
--   1. no output and no queries;
--   2. pointer registers $p_0=n$, $p_1=M$, $p_2=4n$, $p_3=0$, $p_4=\mathrm{cSAMP}(k)$, $p_{10}=0$, $p_{11}=1$, $p_{18}=3k+3$, $p_{43}=3$, $p_{45}=2$, $p_{46}=k$, $p_{47}=4$;
--   3. real registers $r_0=0$, $r_4=4$, $r_5=1$, $r_6=1/M$;
--   4. unchanged real memory;
--   5. integer memory equal to `mem0 n M`, which holds the input and the Pauli multiplication and phase-exponent tables.
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
theorem st0_facts (k n M : ℕ) (ε δ : ℝ) :
    let s := st0 k n M ε δ
    s.output = none ∧ s.durations = [] ∧
    s.core.ptrs 0 = n ∧ s.core.ptrs 1 = M ∧ s.core.ptrs 2 = 4 * n ∧ s.core.ptrs 3 = 0 ∧
    s.core.ptrs 4 = cSAMP k ∧ s.core.ptrs 10 = 0 ∧ s.core.ptrs 11 = 1 ∧
    s.core.ptrs 18 = 3 * k + 3 ∧ s.core.ptrs 43 = 3 ∧ s.core.ptrs 45 = 2 ∧ s.core.ptrs 46 = k ∧
    s.core.ptrs 47 = 4 ∧
    s.core.regs 0 = 0 ∧ s.core.regs 4 = 4 ∧ s.core.regs 5 = 1 ∧ s.core.regs 6 = 1 / M ∧
    s.core.mem = (alg1Input n M ε δ).core.mem ∧
    s.intMem = mem0 n M := by sorry
end LindbladStructLearn.Mach.A1
