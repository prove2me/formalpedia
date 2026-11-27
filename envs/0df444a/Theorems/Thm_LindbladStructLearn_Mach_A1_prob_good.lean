-- Prove2me | Theorems.Thm_LindbladStructLearn_Mach_A1_prob_good
-- name    : LindbladStructLearn.Mach.A1.prob_good
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T02:44:07.015545+00:00
-- url     : https://prove2.me/theorems/22b422cb-f771-4325-99a5-385c5b905290
-- title:
--   Concentration of the empirical estimates
-- statement:
--   Let $\Phi$ be a quantum channel and let $M$ rounds be drawn independently. Each round has probability $p(x)=32^{-n}\mathrm{Re}\,\mathrm{bornAmp}(\Phi,A,v,B,w)$, where the strings $A,v,B$ are uniform and $w$ is the measurement outcome. Then
--   $$\Pr\Big[\forall \bar P,\ |S_{\bar P}|\le k:\ \Big\|\tfrac1M\sum_{i<M}\mathrm{alg1Sample}(\bar P,x_i)-\hat\Phi_{\rm loc}(\bar P)\Big\|\le\varepsilon\Big]\ \ge\ 1-4K\exp\Big(-\frac{M\varepsilon^2}{64\cdot16^k}\Big),$$
--   where $K=(k+1)n^k16^k$ bounds the number of pairs $\bar P$ with $|S_{\bar P}|\le k$. This is a finite Hoeffding bound with a union bound. Proposition 2.9 makes the estimator unbiased, and $|\mathrm{alg1Sample}|\le4^k$.
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
theorem prob_good {n : ℕ} (Φ : Super (Qubits n) (Qubits n)) (hΦ : IsChannel Φ) (k : ℕ) (hn : 1 ≤ n) (M : ℕ)
    (hM : 0 < M) (ε : ℝ) (hε : 0 < ε) :
    1 - 4 * Kc k n * Real.exp (-(M * ε ^ 2) / (64 * 16 ^ k)) ≤
      ∑ ω : Fin M → Rd n, (∏ i, pw Φ (ω i)) *
        (if ∀ Q : Pauli n × Pauli n, (pairSupport Q).card ≤ k → ‖avg ω Q - locFourier Φ Q‖ ≤ ε
          then (1 : ℝ) else 0) := by sorry
end LindbladStructLearn.Mach.A1
