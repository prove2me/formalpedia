-- Prove2me | Theorems.Thm_LindbladStructLearn_Mach_A1_valid_loop
-- name    : LindbladStructLearn.Mach.A1.valid_loop
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T02:44:04.890846+00:00
-- url     : https://prove2.me/theorems/d1830720-5181-452d-81d4-a58c8a20e585
-- title:
--   Record validity loop
-- statement:
--   Starting from $p_{19}=0$ and $p_{41}=1$ (with $p_{46}=k$, $p_{10}=0$, $p_{11}=1$), the loop `loop 46 19 (validBody k)` terminates within $32k+1$ steps. It leaves memory, outputs and real data unchanged and changes only scratch pointers. It ends with
--   $$p_{41}=\begin{cases}0,&\text{if some position }r<k\text{ violates the canonical form},\\1,&\text{otherwise.}\end{cases}$$
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
theorem valid_loop (k : ℕ) (s : MState) (h46 : s.core.ptrs 46 = k) (h10 : s.core.ptrs 10 = 0)
    (h11 : s.core.ptrs 11 = 1) (h19 : s.core.ptrs 19 = 0) (h41 : s.core.ptrs 41 = 1) :
    ∃ s' m, Exec (.loop 46 19 (validBody k)) s s' m ∧ m ≤ k * 32 + 1 ∧ Same s s' ∧
      s'.intMem = s.intMem ∧
      (∀ q, q ≠ 6 → q ≠ 7 → q ≠ 9 → q ≠ 19 → q ≠ 21 → q ≠ 22 → q ≠ 23 → q ≠ 41 →
        s'.core.ptrs q = s.core.ptrs q) ∧
      s'.core.ptrs 41 = if ∃ r : ℕ, r < k ∧ badM (s.core.ptrs 20) r (s.intMem (cDIG k + r + 1))
        (s.intMem (cDIG k + r + 1 + k)) (s.intMem (cDIG k + r + 1 + k + k))
        (s.intMem (cDIG k + (r + 1) + 1)) then 0 else 1 := by sorry
end LindbladStructLearn.Mach.A1
