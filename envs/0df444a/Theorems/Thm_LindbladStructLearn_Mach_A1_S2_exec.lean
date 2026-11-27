-- Prove2me | Theorems.Thm_LindbladStructLearn_Mach_A1_S2_exec
-- name    : LindbladStructLearn.Mach.A1.S2_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T02:43:54.740872+00:00
-- url     : https://prove2.me/theorems/35780ce7-6e92-5fde-a568-71cfbeda3d71
-- title:
--   Record enumeration phase
-- statement:
--   The record-enumeration phase `S2 k` writes all $K=(k+1)n^k16^k$ records. The state must have $n,k$ and the constants in place, the output pointer $p_{12}=p>\mathrm{cDIG}(k)+3k$, and zero digit cells. Then `S2 k` runs within $K(130k+62)+5$ steps, with the following effect.
--   1. Record $j<K$ is written at address $p+1+j(3k+3)$ with cells `recCell k n j i` ($i\le 3k$). These are the digits of the $j$-th odometer state `Dseq k n j`, with size $k+1$ when the record is not canonical.
--   2. The count $K$ is stored at cell $p$, and $p_{14}=K$.
--   3. Integer memory below $p$ (outside the digit cells), real data, outputs and durations are unchanged, and only scratch pointers change.
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
theorem S2_exec (k n : ℕ) (hn : 1 ≤ n) (s : MState) (p : ℤ)
    (h0 : s.core.ptrs 0 = n) (h10 : s.core.ptrs 10 = 0) (h11 : s.core.ptrs 11 = 1)
    (h46 : s.core.ptrs 46 = k) (h18 : s.core.ptrs 18 = 3 * k + 3) (h12 : s.core.ptrs 12 = p)
    (hD : ∀ i ≤ 3 * k, s.intMem (cDIG k + i) = 0) (hp : cDIG k + 3 * k < p) :
    ∃ s' m, Exec (S2 k) s s' m ∧ m ≤ Kc k n * (130 * k + 62) + 5 ∧ Same s s' ∧
      (∀ q, q ∉ scr2 → s'.core.ptrs q = s.core.ptrs q) ∧ s'.core.ptrs 14 = Kc k n ∧
      s'.intMem p = Kc k n ∧
      (∀ j < Kc k n, ∀ i ≤ 3 * k, s'.intMem (recAddr k p j + i) = recCell k n j i) ∧
      (∀ z, (z < cDIG k ∨ cDIG k + 3 * k < z) → z < p → s'.intMem z = s.intMem z) := by sorry
end LindbladStructLearn.Mach.A1
