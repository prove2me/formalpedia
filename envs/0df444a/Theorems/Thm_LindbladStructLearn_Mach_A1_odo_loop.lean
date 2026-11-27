-- Prove2me | Theorems.Thm_LindbladStructLearn_Mach_A1_odo_loop
-- name    : LindbladStructLearn.Mach.A1.odo_loop
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T02:44:02.595655+00:00
-- url     : https://prove2.me/theorems/8f23af3b-8b33-4e26-a6e7-2450ea57881b
-- title:
--   Odometer increment loop
-- statement:
--   The carry loop of the record enumeration implements the mixed-radix increment `incAt` on the digit cells. The radix is $k+1$ at position $0$, $n$ at positions $1..k$, and $4$ above.
--
--   Suppose the digit cells hold $D$, the carry flag is $1$, the done flag is $0$, and the loop starts at position $q\le 3k$. Then the loop terminates within $23(q+1)+1$ steps and the digit cells afterwards hold $(\mathrm{incAt}\,q\,D)_1$. The done flag $p_{40}$ is $1$ exactly when position $0$ overflowed. No memory outside the digit cells changes, and only scratch pointers are modified.
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
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec
theorem odo_loop (k n : ℕ) : ∀ (q : ℕ) (t : MState) (D : ℕ → ℕ), q ≤ 3 * k →
    t.core.ptrs 15 = q → t.core.ptrs 42 = 1 → t.core.ptrs 40 = 0 → t.core.ptrs 46 = k →
    t.core.ptrs 10 = 0 → t.core.ptrs 0 = n → (∀ i ≤ 3 * k, t.intMem (cDIG k + i) = D i) →
    ∃ t' m, Exec (.loop 42 10 (odoBody k)) t t' m ∧ m ≤ (q + 1) * 23 + 1 ∧ Same t t' ∧
      (∀ p, p ≠ 6 → p ≠ 9 → p ≠ 15 → p ≠ 16 → p ≠ 17 → p ≠ 40 → p ≠ 42 →
        t'.core.ptrs p = t.core.ptrs p) ∧
      (∀ i ≤ 3 * k, t'.intMem (cDIG k + i) = (incAt k n q D).1 i) ∧
      (∀ z, (z < cDIG k ∨ cDIG k + 3 * k < z) → t'.intMem z = t.intMem z) ∧
      t'.core.ptrs 40 = if (incAt k n q D).2 then 1 else 0 := by sorry
end LindbladStructLearn.Mach.A1
