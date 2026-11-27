-- Prove2me | Theorems.Thm_LindbladStructLearn_Mach_A1_iterOuter_frame
-- name    : LindbladStructLearn.Mach.A1.iterOuter_frame
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T02:44:10.155689+00:00
-- url     : https://prove2.me/theorems/c3dc5fd8-7c3d-4186-9010-4fa13308f25b
-- title:
--   Frame of the sampling rounds
-- statement:
--   After $r$ sampling rounds from a state with $p_0=n$:
--   1. the output and the real registers and memory are unchanged;
--   2. the durations list gains $r$ copies of $r_0$;
--   3. the work grows by $r(19n+7)$;
--   4. pointer registers outside $\{3,\dots,9\}$ are unchanged, $p_3$ grows by $r$, and $p_4$ grows by $r\,p_2$.
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
theorem iterOuter_frame {n : ℕ} (r : ℕ) (G : Fin r → Rd n) (s : MState) (h0 : s.core.ptrs 0 = n) :
    let t := iterOuter r G s
    t.output = s.output ∧ t.durations = s.durations ++ List.replicate r (s.core.regs 0) ∧
    t.work = s.work + r * (19 * n + 7) ∧ t.core.regs = s.core.regs ∧ t.core.mem = s.core.mem ∧
    (∀ q, q ≠ 3 → q ≠ 4 → q ≠ 5 → q ≠ 6 → q ≠ 7 → q ≠ 8 → q ≠ 9 → t.core.ptrs q = s.core.ptrs q) ∧
    t.core.ptrs 3 = s.core.ptrs 3 + r ∧ t.core.ptrs 4 = s.core.ptrs 4 + r * s.core.ptrs 2 := by sorry
end LindbladStructLearn.Mach.A1
