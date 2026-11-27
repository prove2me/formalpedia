-- Prove2me | Theorems.Thm_LindbladStructLearn_Mach_A1_S3_exec
-- name    : LindbladStructLearn.Mach.A1.S3_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T02:43:53.887644+00:00
-- url     : https://prove2.me/theorems/0617138d-bfdb-46ac-8510-9e2d20de165e
-- title:
--   Estimation phase
-- statement:
--   Suppose the $K$ records are in memory (as written by the enumeration phase), the tables are in memory, and the sample region holds the samples `smp`. Then the estimation phase `S3 k` terminates within $K\,(M(70k+32)+4k+32)+3$ steps. For every valid record $j$, the real cells $b_j+3k+1$ and $b_j+3k+2$ then hold the real and imaginary parts of
--   $$\Big(\sum_{i<M}\mathrm{alg1Sample}\big(\bar P_j,A^{(i)},v^{(i)},B^{(i)},w^{(i)}\big)\Big)\cdot r_6,$$
--   where $\bar P_j$ is the Pauli pair named by record $j$ and $b_j=p+1+j(3k+3)$. Integer memory, outputs, durations and $p_{12}$ are unchanged.
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
theorem S3_exec (s : MState) (k n M : ℕ) (hn : 1 ≤ n) (smp : Fin M → Rd n) (p : ℤ)
    (h10 : s.core.ptrs 10 = 0) (h11 : s.core.ptrs 11 = 1) (h45 : s.core.ptrs 45 = 2)
    (h43 : s.core.ptrs 43 = 3) (h47 : s.core.ptrs 47 = 4) (h46 : s.core.ptrs 46 = k)
    (h0 : s.core.ptrs 0 = n) (h2 : s.core.ptrs 2 = 4 * n) (h1 : s.core.ptrs 1 = M)
    (h18 : s.core.ptrs 18 = 3 * k + 3) (h12 : s.core.ptrs 12 = p) (h14 : s.core.ptrs 14 = Kc k n)
    (hr4 : s.core.regs 4 = 4) (htab : Tab s.intMem)
    (hrecm : ∀ j < Kc k n, ∀ i ≤ 3 * k, s.intMem (recAddr k p j + i) = recCell k n j i)
    (hsm : SampMem k n M smp s.intMem) :
    ∃ s' m, Exec (S3 k) s s' m ∧ m ≤ Kc k n * (M * (70 * k + 32) + 4 * k + 32) + 3 ∧
      s'.output = s.output ∧ s'.durations = s.durations ∧ s'.intMem = s.intMem ∧
      s'.core.ptrs 12 = p ∧
      ∀ j < Kc k n, validD k (Dseq k n j) →
        s'.core.mem (recAddr k p j + (3 * k + 1)) = (tsum k n M smp j).re * s.core.regs 6 ∧
        s'.core.mem (recAddr k p j + (3 * k + 1) + 1) = (tsum k n M smp j).im * s.core.regs 6 := by sorry
end LindbladStructLearn.Mach.A1
