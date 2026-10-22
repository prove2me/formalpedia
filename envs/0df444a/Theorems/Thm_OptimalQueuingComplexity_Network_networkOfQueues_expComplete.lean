-- Prove2me | Theorems.Thm_OptimalQueuingComplexity_Network_networkOfQueues_expComplete
-- name    : OptimalQueuingComplexity.Network.networkOfQueues_expComplete
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T11:01:04.217862+00:00
-- url     : https://prove2.me/theorems/ede34e3a-fbdb-459d-a2fb-b4b7732bdf52
-- title:
--   Theorem 1 — NETWORK OF QUEUES is EXP-complete
-- statement:
--   NETWORK OF QUEUES is EXP-complete. The problem asks whether a closed multiclass queueing network with exponential service times, controlled routing on the classes in $D$, random routing on the classes in $R$, and nonpreemptive sequencing admits a policy whose weighted throughput exceeds $K$. It is in EXP, and every language in EXP polynomial-time many-one reduces to it:
--   $$\text{NETWORK OF QUEUES} \in \mathrm{EXP} \quad\text{and}\quad \forall L \in \mathrm{EXP},\ L \le_p \text{NETWORK OF QUEUES}.$$
--
--   Since EXP strictly contains P (time hierarchy), optimal control of such networks provably requires exponential time in the worst case, independently of the P vs. NP question.
--
--   **Formalization Note.** Instances use a length-faithful binary encoding, and ill-formed instances are no-instances. Zero mean service time means instantaneous service, with ties broken by lowest server index, and zero-mean routing cycles are excluded. Policies are deterministic stationary functions of the network state, and $J^\pi$ is the extended-real $\limsup$ of $\frac1t \sum_c w(c)\,\mathbb{E}[a^\pi_c(t)]$.
-- source:
--   Papadimitriou & Tsitsiklis, The Complexity of Optimal Queuing Network Control, Math. Oper. Res. 24(2) (1999), p. 296, Theorem 1

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Network_EXPComplete
import Definitions.Def_OptimalQueuingComplexity_Network_networkOfQueues

namespace OptimalQueuingComplexity.Network

/-- Theorem 1 (Papadimitriou & Tsitsiklis 1999, p. 296): NETWORK OF QUEUES is EXP-complete. -/
theorem networkOfQueues_expComplete : EXPComplete Instance.enc networkOfQueues := by sorry

end OptimalQueuingComplexity.Network
