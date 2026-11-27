-- Prove2me | Theorems.Thm_LindbladStructLearn_Mach_A1_siteBody_sem
-- name    : LindbladStructLearn.Mach.A1.siteBody_sem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T02:44:01.332808+00:00
-- url     : https://prove2.me/theorems/213d2569-670d-5793-a141-a12e5f756a74
-- title:
--   One site of the sample estimator
-- statement:
--   One pass of the site loop of the estimator processes site $r$ of a record. The record gives the site $x$ and the letters $L_1,L_2$; the current sample gives the letters $A,B$ at site $x$ and the bits $V,W$. Suppose the multiplication and phase tables are in memory. Then the body:
--   1. adds to the phase exponent $p_{31}$ the quantity
--   $$\mathrm{siteExp}=e(L_2,A)+e(L_2A,L_1)+2[A\ne0\wedge V]+2[B\ne0\wedge W],$$
--   where $\mathrm{letterPhase}(a,b)=i^{e(a,b)}$;
--   2. clears the success flag $p_{30}$ unless $B=L_2\,A\,L_1$ (Pauli letter product);
--   3. increments $p_{19}$;
--   4. uses at most $55$ steps and changes only scratch pointers.
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
theorem siteBody_sem (t : MState) (k n : ℕ) (x : ℕ) (L1 L2 A B : Fin 4) (V W : Bool)
    (h10 : t.core.ptrs 10 = 0) (h46 : t.core.ptrs 46 = k) (h0 : t.core.ptrs 0 = n)
    (htab : Tab t.intMem)
    (hx : t.intMem (t.core.ptrs 13 + t.core.ptrs 19 + 1) = x)
    (hl1 : t.intMem (t.core.ptrs 13 + t.core.ptrs 19 + 1 + k) = (L1 : ℕ))
    (hl2 : t.intMem (t.core.ptrs 13 + t.core.ptrs 19 + 1 + k + k) = (L2 : ℕ))
    (hA : t.intMem (t.core.ptrs 4 + x) = (A : ℕ))
    (hV : t.intMem (t.core.ptrs 4 + x + n) = if V then 1 else 0)
    (hB : t.intMem (t.core.ptrs 4 + x + n + n) = (B : ℕ))
    (hW : t.intMem (t.core.ptrs 4 + x + n + n + n) = if W then 1 else 0) :
    let v := siteBody.fin t
    Same t v ∧ v.intMem = t.intMem ∧ t.work ≤ v.work ∧ v.work ≤ t.work + 55 ∧
    (∀ q, q ≠ 6 → q ≠ 7 → q ≠ 8 → q ≠ 9 → q ≠ 19 → q ≠ 21 → q ≠ 22 → q ≠ 23 → q ≠ 24 → q ≠ 25 →
      q ≠ 26 → q ≠ 27 → q ≠ 28 → q ≠ 29 → q ≠ 30 → q ≠ 31 → v.core.ptrs q = t.core.ptrs q) ∧
    v.core.ptrs 19 = t.core.ptrs 19 + 1 ∧
    v.core.ptrs 30 = (if B = letterMul (letterMul L2 A) L1 then t.core.ptrs 30 else 0) ∧
    v.core.ptrs 31 = t.core.ptrs 31 + (siteExp L1 L2 A B V W : ℕ) := by sorry
end LindbladStructLearn.Mach.A1
