-- Prove2me | Theorems.Thm_HordijkKallenbergLP_SingleLP_theorem_2a_gain
-- name    : HordijkKallenbergLP.SingleLP.theorem_2a_gain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:52:12.485979+00:00
-- url     : https://prove2.me/theorems/a46f5e13-250b-4d41-8556-e553940c5efa
-- title:
--   Theorem 2a (p. 355) — φ(f^∞) = P*(f)r(f)
-- statement:
--   Let $f$ be a decision rule with $f(i)\in A(i)$, $P(f)=(p_{if(i)j})$ and $r(f)=(r_{if(i)})$, and let
--   $$P^*(f)=\lim_{n\to\infty}\frac1n\sum_{k=1}^n P^{k-1}(f)$$
--   be the Cesàro limit matrix. Then the average expected reward of the pure stationary policy $f^\infty$ is
--   $$\varphi(f^\infty)=P^*(f)\,r(f),$$
--   that is, $\varphi_i(f^\infty)=\big(P^*(f)r(f)\big)_i$ for every state $i$.
--
--   This identity converts the average reward of a stationary policy into linear algebra and closes the proof of Theorem 7.
--
--   **Formalization Note** The other clauses of Theorem 2 (existence of $P^*(f)$, $PP^*=P^*P=P^*P^*=P^*$, existence of $D(f)$ and $P^*D=0$) are Blackwell's Lemma 1(a), (d), referenced in this mission. $\varphi_i(f^\infty)$ is the lim inf average reward of the history-dependent model.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 355, Theorem 2a

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_SingleLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology

namespace HordijkKallenbergLP.SingleLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Theorem 2a, last clause (Kemeny and Snell; Blackwell).** For a pure and stationary policy
`f^∞`, `φ(f^∞) = P*(f) r(f)`: the lim inf average expected reward of `f^∞` from state `i` is the
`i`-th entry of the limit matrix `P*(f) = lim_n (1/n) Σ_{k=1}^n P^{k−1}(f)` applied to `r(f)`.

Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci.
25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 355, Theorem 2a.

**Formalization Note.** The remaining clauses of Theorem 2 (existence of `P*(f)`, the identities
`P P* = P* P = P* P* = P*`, existence of `D(f)` and `P* D = 0`) are the published Blackwell
Lemma 1(a), (d) for an arbitrary Markov matrix and are not restated. -/
theorem theorem_2a_gain (M : StationaryMDP S A) [Nonempty S] (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) :
    ∀ i : S, gainInf (stationaryPolicy M f hf) i
      = (limitMatrix (transMatrix M f) *ᵥ rewardVec M f) i := by sorry

end HordijkKallenbergLP.SingleLP
