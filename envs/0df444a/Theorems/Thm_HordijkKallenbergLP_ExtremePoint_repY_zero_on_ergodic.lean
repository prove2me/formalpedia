-- Prove2me | Theorems.Thm_HordijkKallenbergLP_ExtremePoint_repY_zero_on_ergodic
-- name    : HordijkKallenbergLP.ExtremePoint.repY_zero_on_ergodic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:57:37.480491+00:00
-- url     : https://prove2.me/theorems/771541cc-88c5-42f6-a7ba-f89ccf63edca
-- title:
--   Proof of Theorem 10, p. 362 — by definition of γ, ȳ(f) vanishes at some state of every ergodic set of P(f)
-- statement:
--   Let $\beta_j>0$ with $\sum_j\beta_j=1$, let $f^\infty$ be a pure stationary policy ($f(i)\in A(i)$), and let $\bar y_i(f)=y_{if(i)}(f)$ be the $y$-part of its representative (6) read along $f$. For every ergodic set $E_k$ of $P(f)$ there is a state $i(k)\in E_k$ with
--   $$
--   \bar y_{i(k)}(f)=0.
--   $$
--
--   This zero is what the choice of $\gamma$ in (6) is for: it anchors the uniqueness argument on each ergodic set in the proof of Theorem 10.
--
--   **Formalization Note.** Ergodic sets are the sets of states accessible from a recurrent state of $P(f)$. The vector $\gamma$ uses the denominator $\sum_{k\in E_j}p^*_{ki}$; with the printed $\sum_k p^*_{ki}$ the zero need not exist.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 362, proof of Theorem 10

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_ExtremePoint_Model
open Matrix MarkovDecisionProcesses BlackwellDiscreteDP.NearOne

namespace HordijkKallenbergLP.ExtremePoint

/-- **Proof of Theorem 10, p. 362 (unnumbered): a zero of `ȳ(f)` on every ergodic set.** Let
`f^∞` be a pure stationary policy (`f(i) ∈ A(i)`) and `P = P(f)`. On every ergodic set `E_k`
of `P` there is a state `i(k)` with `ȳ_{i(k)}(f) = y_{i(k) f(i(k))}(f) = 0`, where `y(f)` is the
`y`-part of the representative (6).

Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci.
25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 362, proof of Theorem 10
("By definition of γ, there is on each E_k a state i(k) such that ȳ_{i(k)}(f) = 0;").

**Formalization Note.** The ergodic sets are the sets `ergodicSet P l` of states accessible from a
recurrent `l`; `P(f)` is `policyMatrix M (pureRule f)`, which equals
`(p_{if(i)j})` = `transMatrix M f`. `γ` uses the corrected denominator `∑_{k ∈ E_j} p*_ki`
(see `gamma`); with the printed `∑_k p*_ki` this zero need not exist. -/
theorem repY_zero_on_ergodic {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] (M : StationaryMDP S A) (β : S → ℝ) (hβpos : ∀ j, 0 < β j)
    (hβsum : ∑ j, β j = 1) (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) (l : S)
    (hl : IsRecurrent (policyMatrix M (pureRule f)) l) :
    ∃ i ∈ ergodicSet (policyMatrix M (pureRule f)) l,
      repY M β (pureRule f) ⟨(i, f i), hf i⟩ = 0 := by sorry

end HordijkKallenbergLP.ExtremePoint
