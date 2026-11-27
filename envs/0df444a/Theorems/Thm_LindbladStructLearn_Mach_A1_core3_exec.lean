-- Prove2me | Theorems.Thm_LindbladStructLearn_Mach_A1_core3_exec
-- name    : LindbladStructLearn.Mach.A1.core3_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T02:44:25.609074+00:00
-- url     : https://prove2.me/theorems/6f9465e3-6311-4050-a04b-44a7c49f4fb5
-- title:
--   Estimate of one valid record
-- statement:
--   For a record of size $S$ (sites and letters as above), suppose the sample region holds $M$ samples. Then the estimation body `core3 k` terminates within $M(70S+32)+4S+20$ steps. It writes $\mathrm{tot}.\mathrm{re}\cdot r_6$ and $\mathrm{tot}.\mathrm{im}\cdot r_6$ to the real cells $b+3k+1$ and $b+3k+2$ of the record, where
--   $$\mathrm{tot}=\sum_{i<M}\mathrm{contrib}_i,\qquad \mathrm{contrib}_i=\mathbf 1\big[\forall r<S,\ B^{(i)}_r=L_{2,r}A^{(i)}_rL_{1,r}\big]\;4^{S}\,i^{\sum_r\mathrm{siteExp}^{(i)}_r}.$$
--   Integer memory, outputs, durations and the other real registers (except $r_1,r_2,r_3$) are unchanged.
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
theorem core3_exec (t : MState) (k n S M : ℕ) (xs : ℕ → ℕ) (L1f L2f : ℕ → Fin 4)
    (Af Bf : ℕ → ℕ → Fin 4) (Vf Wf : ℕ → ℕ → Bool)
    (h10 : t.core.ptrs 10 = 0) (h11 : t.core.ptrs 11 = 1) (h45 : t.core.ptrs 45 = 2)
    (h43 : t.core.ptrs 43 = 3) (h47 : t.core.ptrs 47 = 4) (h46 : t.core.ptrs 46 = k)
    (h0 : t.core.ptrs 0 = n) (h2 : t.core.ptrs 2 = 4 * n) (h20 : t.core.ptrs 20 = S)
    (h1 : t.core.ptrs 1 = M) (hr4 : t.core.regs 4 = 4)
    (htab : Tab t.intMem)
    (hrec : ∀ r < S, t.intMem (t.core.ptrs 13 + r + 1) = xs r ∧
      t.intMem (t.core.ptrs 13 + r + 1 + k) = (L1f r : ℕ) ∧
      t.intMem (t.core.ptrs 13 + r + 1 + k + k) = (L2f r : ℕ))
    (hsm : ∀ i < M, ∀ r < S, t.intMem (cSAMP k + 4 * n * i + xs r) = (Af i r : ℕ) ∧
      t.intMem (cSAMP k + 4 * n * i + xs r + n) = (if Vf i r then 1 else 0) ∧
      t.intMem (cSAMP k + 4 * n * i + xs r + n + n) = (Bf i r : ℕ) ∧
      t.intMem (cSAMP k + 4 * n * i + xs r + n + n + n) = (if Wf i r then 1 else 0)) :
    let tot := ∑ i ∈ Finset.range M, contrib S L1f L2f (Af i) (Bf i) (Vf i) (Wf i)
    let b := t.core.ptrs 13
    ∃ t' m, Exec (core3 k) t t' m ∧ m ≤ M * (70 * S + 32) + 4 * S + 20 ∧
      t'.output = t.output ∧ t'.durations = t.durations ∧ t'.intMem = t.intMem ∧
      (∀ q, q ∉ ({1, 2, 3} : Finset ℕ) → t'.core.regs q = t.core.regs q) ∧
      (∀ q, q ∉ scrS → q ≠ 4 → q ≠ 7 → q ≠ 34 → t'.core.ptrs q = t.core.ptrs q) ∧
      t'.core.mem = Function.update (Function.update t.core.mem (b + (3 * k + 1))
        (tot.re * t.core.regs 6)) (b + (3 * k + 1) + 1) (tot.im * t.core.regs 6) := by sorry
end LindbladStructLearn.Mach.A1
