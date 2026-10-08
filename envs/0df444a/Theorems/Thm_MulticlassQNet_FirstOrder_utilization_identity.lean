-- Prove2me | Theorems.Thm_MulticlassQNet_FirstOrder_utilization_identity
-- name    : MulticlassQNet.FirstOrder.utilization_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:36:35.782983+00:00
-- url     : https://prove2.me/theorems/9478beec-5b01-439c-a299-137809f23728
-- title:
--   §4.2, p. 19 — steady-state utilization E[1{B_r}] = λ_r/μ_r
-- statement:
--   Consider an open multiclass network with external rates $\lambda_{0r}$, routing $p_{rs}$ and service rates $\mu_r$, let $\lambda$ be the solution of the traffic equations (15), and assume the load condition $\sum_{r\in C_i}\lambda_r/\mu_r<1$ at every station. Let a Markovian sequencing policy satisfy Assumption A with invariant distribution $\pi$, and let $B_r$ be the event that station $\sigma(r)$ is serving a class-$r$ job. Then for every class $r$,
--   $$E_\pi\big[1\{B_r\}\big]=\frac{\lambda_r}{\mu_r}.$$
--
--   In words: in steady state the fraction of time a station spends serving class $r$ is the class's offered load, whatever the policy. The paper uses this relation in the proofs of Theorems 4.1 and 4.2.
--
--   **Formalization Note** $\lambda$ is an input constrained by (15) and openness (uniqueness of the traffic solution), never defined from the policy. The expectation is a `tsum` against $\pi$.
-- source:
--   Bertsimas, Paschalidis, Tsitsiklis, Optimization of Multiclass Queueing Networks: Polyhedral and Nonlinear Characterizations of Achievable Performance, MIT Sloan WP #3509-92-MSA (Dec. 1992), p. 19, §4.2, proof of Theorem 4.2, first display (also p. 16, proof of Theorem 4.1)

import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Dynamics

namespace MulticlassQNet.FirstOrder

/-- Utilization identity (§4.2, proof of Theorem 4.2, p. 19): in steady state
`E[1{B_r}] = λ_r / μ_r`, where `λ` solves the traffic equations (15). -/
theorem utilization_identity {N R : ℕ} (net : Network N R) (lam : Fin R → ℝ)
    (htraffic : net.IsTrafficSolution lam) (hopen : net.IsOpen) (hload : net.LoadLtOne lam)
    (P : Policy net) (π : (Fin R → ℕ) → ℝ) (hA : P.AssumptionA π) :
    ∀ r, P.busyProb π r = lam r / net.μ r := by sorry

end MulticlassQNet.FirstOrder
