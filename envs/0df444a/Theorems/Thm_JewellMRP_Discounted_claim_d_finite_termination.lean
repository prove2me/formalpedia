-- Prove2me | Theorems.Thm_JewellMRP_Discounted_claim_d_finite_termination
-- name    : JewellMRP.Discounted.claim_d_finite_termination
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:02:42.275707+00:00
-- url     : https://prove2.me/theorems/8eaaf17a-191f-4c11-8d5c-4062eb3a4755
-- title:
--   Claim (d), p. 946 — the algorithm of Fig. 1 terminates in a finite number of cycles
-- statement:
--   Let a Markov-renewal program with $N$ states and $Z$ alternatives be given and let $\alpha > 0$. For every run $(d_k, v_k)_{k \ge 0}$ of the algorithm of Fig. 1 (each $v_k$ solves (15) for $d_k$, and $d_{k+1}$ is obtained from $d_k$ and $v_k$ by the policy-improvement step with the retention rule), there is a cycle $K$ with
--   $$
--   d_{K+1} = d_K \qquad\text{and}\qquad K < Z^N ,
--   $$
--   where $Z^N$ is the number of stationary policies.
--
--   The paper writes "(d) The algorithm terminates in a finite number of cycles", justified by "the fact that there are only a finite number of policies". The bound $K < Z^N$ makes "finite" explicit using the paper's own count of stationary policies (p. 946: "there are $Z^N$ of them").
--
--   **Formalization Note** The algorithm is modelled as an infinite sequence of cycles; termination means that two successive policies coincide, which is the "Done" test of Fig. 1. The retention rule is essential: without it the iterates may alternate forever between two policies that tie. The bound $K < Z^N$ is written as $K$ less than the cardinality of the type of maps from states to alternatives.
-- source:
--   Jewell, Markov-Renewal Programming. I: Formulation, Finite Return Models, Operations Research 11(6), 1963, p. 946, Claim (d)

import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP
import Definitions.Def_JewellMRP_Discounted_PolicyIteration

open Filter Topology

namespace JewellMRP.Discounted

/-- Claim (d), p. 946: every run of the algorithm of Fig. 1 produces two identical successive
policies within at most as many cycles as there are stationary policies. -/
theorem claim_d_finite_termination {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [Nonempty A] (M : MRP S A) {α : ℝ} (hα : 0 < α) {d : ℕ → S → A} {v : ℕ → S → ℝ}
    (hrun : IsFig1Run M α d v) :
    ∃ K, K < Fintype.card (S → A) ∧ d (K + 1) = d K := by sorry

end JewellMRP.Discounted
