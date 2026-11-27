-- Prove2me | Theorems.Thm_LindbladStructLearn_Mach_A1_tail
-- name    : LindbladStructLearn.Mach.A1.tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T02:44:04.951842+00:00
-- url     : https://prove2.me/theorems/96621ee1-3901-4bf4-b8ee-34435949e910
-- title:
--   Record and estimation phases until halting
-- statement:
--   From the record-phase entry state `xEnd` for round data $G$, the program runs deterministically for at most
--   $$K(130k+62)+5+K\big(M(70k+32)+4k+32\big)+3+1$$
--   steps, with $K=(k+1)n^k16^k$. It reaches a halted state $H$ (mass and reachability are transported along this run) with:
--   1. output pointer $\mathrm{cSAMP}(k)+4nM$, durations equal to $M$ zeros, and the record count $K$;
--   2. all $K$ records in place;
--   3. for each valid record $j$, the value $\frac1M\sum_i\mathrm{alg1Sample}(\bar P_j,\text{sample }i)$ in its real cells.
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
theorem tail {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)} (k M : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (G : Fin M → Rd n) :
    ∃ H : MState, ∃ m : ℕ, m ≤ Kc k n * (130 * k + 62) + 5 + (Kc k n * (M * (70 * k + 32) + 4 * k + 32) + 3) + 1 ∧
      (∀ N E, mass (prog k) n evo (N + m) (setpc (xEnd k n M ε δ G) 96) E = mass (prog k) n evo N H E) ∧
      (∀ N x, Reach (prog k) n evo (N + m) (setpc (xEnd k n M ε δ G) 96) x ↔ Reach (prog k) n evo N H x) ∧
      Halted H ∧ H.output = some (pEnd k n M) ∧ H.durations = List.replicate M 0 ∧
      H.work = (xEnd k n M ε δ G).work + m ∧
      H.intMem (pEnd k n M) = Kc k n ∧
      (∀ j < Kc k n, ∀ i ≤ 3 * k, H.intMem (recAddr k (pEnd k n M) j + i) = recCell k n j i) ∧
      (∀ j < Kc k n, validD k (Dseq k n j) →
        H.core.mem (recAddr k (pEnd k n M) j + (3 * k + 1)) = (tsum k n M G j).re * (1 / M) ∧
        H.core.mem (recAddr k (pEnd k n M) j + (3 * k + 1) + 1) = (tsum k n M G j).im * (1 / M)) := by sorry
end LindbladStructLearn.Mach.A1
