-- Prove2me | Theorems.Thm_HordijkKallenbergLP_SingleLP_theorem_7_primal_phi
-- name    : HordijkKallenbergLP.SingleLP.theorem_7_primal_phi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:59:30.689595+00:00
-- url     : https://prove2.me/theorems/3932cb4b-37ec-485b-8421-17b85ffad347
-- title:
--   Proof of Theorem 7 (p. 357) — every primal optimal (φ̄, u) has φ̄ = φ
-- statement:
--   Let $\beta_j>0$ with $\sum_j\beta_j=1$, and let $(\bar\varphi,u)$ be an optimal solution of the primal program. Then
--   $$\bar\varphi=\varphi ,$$
--   the optimal average reward $\varphi_i=\sup_R\varphi_i(R)$.
--
--   So the first component of every primal optimum is the value of the average-reward problem; the proof of Theorem 7 derives this from Theorem 6.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 357, §3.2, proof of Theorem 7

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_SingleLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology

namespace HordijkKallenbergLP.SingleLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Proof of Theorem 7: the φ-part of a primal optimum.** Let `(φ̄, u)` be an optimal solution
of the primal problem. From Theorem 6 it follows that `φ̄ = φ`, the optimal average reward.

Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci.
25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 357, §3.2, proof of Theorem 7 (unnumbered). -/
theorem theorem_7_primal_phi (M : StationaryMDP S A) [Nonempty S]
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1)
    (φbar u : S → ℝ) (hP : IsPrimalOptimal M β φbar u) :
    φbar = optGainInf M := by sorry

end HordijkKallenbergLP.SingleLP
