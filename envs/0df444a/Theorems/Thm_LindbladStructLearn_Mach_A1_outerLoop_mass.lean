-- Prove2me | Theorems.Thm_LindbladStructLearn_Mach_A1_outerLoop_mass
-- name    : LindbladStructLearn.Mach.A1.outerLoop_mass
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T02:43:53.369188+00:00
-- url     : https://prove2.me/theorems/10d53291-f9b4-583a-92e1-5ca951360310
-- title:
--   Sampling rounds as a weighted sum
-- statement:
--   Let $s$ be a state at the sampling loop (pc $71$) with no output, $p_0=n$, $r_0=0$ and at least $r$ rounds remaining. Then after $r(18n+7)$ steps the success mass of any event $E$ splits as a sum over the round data $G\in((\mathbb F_2^5)^n\times\{0,1\}^n)^r$:
--   $$\mathrm{mass}_{N+r(18n+7)}(s,E)=\sum_G\Big(\prod_{i<r}\mathrm{wt}(G_i)\Big)\,\mathrm{mass}_N(s_G,E).$$
--   Here $\mathrm{wt}(g,w)=32^{-n}\,\mathrm{Re}\,\mathrm{bornAmp}(\Phi,A(g),v(g),B(g),w)$, and $s_G$ is the state after the rounds `iterOuter r G s`.
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
theorem outerLoop_mass {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)} (k N : ℕ) (E : MState → Prop) : ∀ (r : ℕ) (s : MState),
    s.output = none → s.core.ptrs 0 = n → s.core.regs 0 = 0 → s.core.ptrs 3 + r ≤ s.core.ptrs 1 →
    mass (prog k) n evo (N + r * (18 * n + 7)) (setpc s 71) E =
      ∑ G : Fin r → Rd n, (∏ i, wt evo (G i).1 (G i).2) *
        mass (prog k) n evo N (setpc (iterOuter r G s) 71) E := by sorry
end LindbladStructLearn.Mach.A1
