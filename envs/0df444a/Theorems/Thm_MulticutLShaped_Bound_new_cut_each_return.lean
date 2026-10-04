-- Prove2me | Theorems.Thm_MulticutLShaped_Bound_new_cut_each_return
-- name    : MulticutLShaped.Bound.new_cut_each_return
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:39:06.344634+00:00
-- url     : https://prove2.me/theorems/ac01ef6a-547d-4278-a4b2-8a772cb49f82
-- title:
--   Proof of the Theorem — every return from Step 3 records a new cut
-- statement:
--   Let one major iteration of the multicut algorithm return to Step 1 from Step 3. Then
--   1. for every scenario $k$, its list of optimality cuts is either unchanged or extended by one cut $c\in\mathcal C_k$ that was not already in the list;
--   2. at least one scenario's list is extended in this way.
--
--   Consequently the cuts recorded for scenario $k$ are distinct elements of the finite set $\mathcal C_k$, and their total number grows by at least one at each return from Step 3. This is the step "in the worst case, one facet of each $Q_k$ is identified in each step" in the proof of the paper's Theorem.
-- source:
--   Birge and Louveaux, A multicut algorithm for two-stage stochastic linear programs, Eur. J. Oper. Res. 34 (1988), p. 388, Section 4, proof of the Theorem

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_LShaped_Bases
import Definitions.Def_MulticutLShaped_Bound_Cuts
import Definitions.Def_MulticutLShaped_Bound_Masters
import Definitions.Def_MulticutLShaped_Bound_Algorithm

namespace MulticutLShaped.Bound

open StochasticProg.Recourse StochasticProg.LShaped

theorem new_cut_each_return {n1 n2 m1 m2 K : ℕ} (inst : Instance n1 n2 m1 m2 K)
    (s s' : State n1 K) (hstep : Step inst s s') (hret : s'.nOpt = s.nOpt + 1) :
    (∀ k, s'.optCuts k = s.optCuts k ∨
      ∃ c ∈ cutSet inst k, c ∉ s.optCuts k ∧ s'.optCuts k = s.optCuts k ++ [c]) ∧
    ∃ k, ∃ c ∈ cutSet inst k, c ∉ s.optCuts k ∧ s'.optCuts k = s.optCuts k ++ [c] := by sorry

end MulticutLShaped.Bound
