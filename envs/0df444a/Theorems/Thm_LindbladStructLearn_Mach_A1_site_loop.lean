-- Prove2me | Theorems.Thm_LindbladStructLearn_Mach_A1_site_loop
-- name    : LindbladStructLearn.Mach.A1.site_loop
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T02:44:24.003071+00:00
-- url     : https://prove2.me/theorems/3ecfa050-502f-4674-bf5a-3f380317a466
-- title:
--   Site loop of the sample estimator
-- statement:
--   For a record of size $S$ whose sites and letters, and the current sample's letters and bits at those sites, are given by functions of $r<S$, the site loop terminates within $57S+1$ steps. Afterwards:
--   1. $p_{30}$ is unchanged if $B_r=L_{2,r}A_rL_{1,r}$ for every $r<S$, and $0$ otherwise;
--   2. $p_{31}$ has increased by $\sum_{r<S}\mathrm{siteExp}_r$.
--
--   Memory and real data are unchanged.
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
theorem site_loop (t : MState) (k n S : ℕ) (xs : ℕ → ℕ) (L1f L2f Af Bf : ℕ → Fin 4) (Vf Wf : ℕ → Bool)
    (h10 : t.core.ptrs 10 = 0) (h46 : t.core.ptrs 46 = k) (h0 : t.core.ptrs 0 = n)
    (h19 : t.core.ptrs 19 = 0) (h20 : t.core.ptrs 20 = S) (htab : Tab t.intMem)
    (hm : ∀ r < S, t.intMem (t.core.ptrs 13 + r + 1) = xs r ∧
      t.intMem (t.core.ptrs 13 + r + 1 + k) = (L1f r : ℕ) ∧
      t.intMem (t.core.ptrs 13 + r + 1 + k + k) = (L2f r : ℕ) ∧
      t.intMem (t.core.ptrs 4 + xs r) = (Af r : ℕ) ∧
      t.intMem (t.core.ptrs 4 + xs r + n) = (if Vf r then 1 else 0) ∧
      t.intMem (t.core.ptrs 4 + xs r + n + n) = (Bf r : ℕ) ∧
      t.intMem (t.core.ptrs 4 + xs r + n + n + n) = (if Wf r then 1 else 0)) :
    ∃ t' m, Exec (.loop 20 19 siteBody) t t' m ∧ m ≤ S * 57 + 1 ∧ Same t t' ∧ t'.intMem = t.intMem ∧
      (∀ q, q ∉ scrS → t'.core.ptrs q = t.core.ptrs q) ∧
      t'.core.ptrs 30 = (if ∀ r < S, Bf r = letterMul (letterMul (L2f r) (Af r)) (L1f r)
        then t.core.ptrs 30 else 0) ∧
      t'.core.ptrs 31 = t.core.ptrs 31 +
        ((∑ r ∈ Finset.range S, siteExp (L1f r) (L2f r) (Af r) (Bf r) (Vf r) (Wf r) : ℕ) : ℤ) := by sorry
end LindbladStructLearn.Mach.A1
