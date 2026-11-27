-- Prove2me | Theorems.Thm_LindbladStructLearn_Mach_A1_validBody_fin
-- name    : LindbladStructLearn.Mach.A1.validBody_fin
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T02:43:59.627227+00:00
-- url     : https://prove2.me/theorems/5c48daee-c841-450e-bde9-cbd00f6a4f61
-- title:
--   Validity test at one record position
-- statement:
--   One pass of the record-validity loop body checks position $r$ (the value of pointer register $19$) of the digit vector held in the digit cells starting at $c=\mathrm{cDIG}(k)$. Let $s_0$ be pointer register $20$ (the record size), and let $x,y,z$ and $x'$ be the cells at $c+r+1$, $c+r+1+k$, $c+r+1+2k$ and $c+r+2$ (site, two letters, next site).
--
--   Run from a state $t$ with $p_{46}=k$, $p_{10}=0$ and $p_{11}=1$, the body:
--   1. leaves the integer memory, outputs, durations, real registers and real memory unchanged;
--   2. uses at most $30$ steps;
--   3. changes no pointer register outside $\{6,7,9,19,21,22,23,41\}$;
--   4. increments $p_{19}$;
--   5. sets $p_{41}$ to $0$ exactly when position $r$ violates the canonical form (predicate `badM`). The canonical form requires zero padding beyond the size, a nonzero letter pair at each used site, and strictly increasing sites.
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
theorem validBody_fin (k : ℕ) (t : MState) (h46 : t.core.ptrs 46 = k) (h10 : t.core.ptrs 10 = 0)
    (h11 : t.core.ptrs 11 = 1) :
    let u := (validBody k).fin t
    let r := t.core.ptrs 19
    Same t u ∧ u.intMem = t.intMem ∧ t.work ≤ u.work ∧ u.work ≤ t.work + 30 ∧
    (∀ q, q ≠ 6 → q ≠ 7 → q ≠ 9 → q ≠ 19 → q ≠ 21 → q ≠ 22 → q ≠ 23 → q ≠ 41 →
      u.core.ptrs q = t.core.ptrs q) ∧ u.core.ptrs 19 = r + 1 ∧
    u.core.ptrs 41 = (if badM (t.core.ptrs 20) r (t.intMem (cDIG k + r + 1))
      (t.intMem (cDIG k + r + 1 + k)) (t.intMem (cDIG k + r + 1 + k + k))
      (t.intMem (cDIG k + (r + 1) + 1)) then 0 else t.core.ptrs 41) := by sorry
end LindbladStructLearn.Mach.A1
