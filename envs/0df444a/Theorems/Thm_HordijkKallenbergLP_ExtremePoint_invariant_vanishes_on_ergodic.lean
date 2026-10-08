-- Prove2me | Theorems.Thm_HordijkKallenbergLP_ExtremePoint_invariant_vanishes_on_ergodic
-- name    : HordijkKallenbergLP.ExtremePoint.invariant_vanishes_on_ergodic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:58:02.827542+00:00
-- url     : https://prove2.me/theorems/24a67642-76b0-481d-bd40-39572a3d757e
-- title:
--   Proof of Theorem 10, p. 362 — an invariant row vector on an ergodic set that vanishes at one state vanishes on the set
-- statement:
--   Let $P=(p_{li})$ be a stochastic matrix on a finite set and $C$ the ergodic set of a recurrent state. If a real vector $z$ satisfies
--   $$
--   z_i=\sum_{l\in C}z_l\,p_{li},\quad i\in C,\qquad\text{and}\qquad z_{i_0}=0\ \text{for some } i_0\in C,
--   $$
--   then $z_i=0$ for every $i\in C$.
--
--   This is the fact from the theory of Markov chains (Chung, *Markov Chains with Stationary Transition Probabilities*, p. 33) that the paper applies to $z=\bar y^1-\bar y^2$ to conclude $\bar y^1=\bar y^2$ in the proof of Theorem 10: on a closed communicating class the invariant row vectors form a one-dimensional space spanned by a strictly positive vector.
--
--   **Formalization Note.** No sign condition is imposed on $z$. The ergodic set is the set of states accessible from the recurrent state.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 362, proof of Theorem 10 (citing Chung [2, p. 33])

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_ExtremePoint_Model
open Matrix MarkovDecisionProcesses BlackwellDiscreteDP.NearOne

namespace HordijkKallenbergLP.ExtremePoint

/-- **Proof of Theorem 10, p. 362 (unnumbered; Chung [2, p. 33]): an invariant row vector on an
ergodic set that vanishes at one state vanishes on the set.** Let `P` be a Markov matrix and
`C = E_k` the ergodic set of a recurrent state `l`. If `z` satisfies
`z_i = ∑_{l' ∈ C} z_{l'} p_{l' i}` for every `i ∈ C`, and `z_{i₀} = 0` for some `i₀ ∈ C`, then
`z_i = 0` for every `i ∈ C`.

Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci.
25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 362, proof of Theorem 10
("ȳ¹_i − ȳ²_i = Σ_{l∈E_k} (ȳ¹_l − ȳ²_l) p_li, i ∈ E_k, ȳ¹_{i(k)} − ȳ²_{i(k)} = 0. Then it follows
from the theory of Markov chains (e.g. Chung [2, p. 33]) that ȳ¹ = ȳ².").

**Formalization Note.** The paper applies the fact to `z = ȳ¹ − ȳ²`; this is the Markov-chain
fact it cites, stated for an arbitrary real `z` (no sign condition). The ergodic set is
`ergodicSet P l`, the states accessible from the recurrent state `l`. -/
theorem invariant_vanishes_on_ergodic {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : IsMarkovMatrix P) (l : n) (hl : IsRecurrent P l) (z : n → ℝ)
    (hz : ∀ i ∈ ergodicSet P l, z i = ∑ k ∈ ergodicSet P l, z k * P k i)
    (i₀ : n) (hi₀ : i₀ ∈ ergodicSet P l) (hz₀ : z i₀ = 0) :
    ∀ i ∈ ergodicSet P l, z i = 0 := by sorry

end HordijkKallenbergLP.ExtremePoint
