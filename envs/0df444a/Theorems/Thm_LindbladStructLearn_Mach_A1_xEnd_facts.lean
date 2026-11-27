-- Prove2me | Theorems.Thm_LindbladStructLearn_Mach_A1_xEnd_facts
-- name    : LindbladStructLearn.Mach.A1.xEnd_facts
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T02:44:08.689892+00:00
-- url     : https://prove2.me/theorems/91e3f3ee-2489-4a88-93e7-566cea4bfa40
-- title:
--   State entering the record phase
-- statement:
--   For any round data $G$, the state `xEnd` reached after initialisation, the $M$ sampling rounds and the exit step satisfies:
--   1. no output, durations equal to $M$ zeros, and work $73+M(19n+7)$;
--   2. the pointer constants needed later and output pointer $p_{12}=\mathrm{cSAMP}(k)+4nM$;
--   3. real registers $r_4=4$ and $r_6=1/M$;
--   4. zero digit cells;
--   5. the multiplication and phase tables in memory;
--   6. the samples of $G$ stored in the sample region (predicate `SampMem`).
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
theorem xEnd_facts (k n M : ℕ) (ε δ : ℝ) (G : Fin M → Rd n) :
    let s := xEnd k n M ε δ G
    s.output = none ∧ s.durations = List.replicate M 0 ∧ s.work = 71 + M * (19 * n + 7) + 1 + 1 ∧
    s.core.ptrs 0 = n ∧ s.core.ptrs 1 = M ∧ s.core.ptrs 2 = 4 * n ∧ s.core.ptrs 3 = M ∧
    s.core.ptrs 10 = 0 ∧ s.core.ptrs 11 = 1 ∧ s.core.ptrs 12 = pEnd k n M ∧
    s.core.ptrs 18 = 3 * k + 3 ∧ s.core.ptrs 43 = 3 ∧ s.core.ptrs 45 = 2 ∧ s.core.ptrs 46 = k ∧
    s.core.ptrs 47 = 4 ∧ s.core.regs 4 = 4 ∧ s.core.regs 6 = 1 / M ∧
    (∀ i ≤ 3 * k, s.intMem (cDIG k + i) = 0) ∧ Tab s.intMem ∧ SampMem k n M G s.intMem := by sorry
end LindbladStructLearn.Mach.A1
