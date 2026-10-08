-- Prove2me | Theorems.Thm_MulticlassQNet_FirstOrder_theorem_4_3_idle_busy_split
-- name    : MulticlassQNet.FirstOrder.theorem_4_3_idle_busy_split
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:36:56.619988+00:00
-- url     : https://prove2.me/theorems/483b008b-a47d-4d04-bf16-3de433031401
-- title:
--   Theorem 4.3 — Σ_{r∈C_i} I_rr' + N_ir' = λ_r' x_r'
-- statement:
--   Consider an open multiclass network with traffic solution $\lambda$ of (15) and the load condition of §4.1, and a Markovian sequencing policy satisfying Assumption A with invariant distribution $\pi$. With $I_{rr'}=E_\pi[1\{B_r\}n_{r'}]$, $N_{ir'}=E_\pi[1\{B_{0i}\}n_{r'}]$ (where $B_{0i}$ is the event that station $i$ is idle) and $\bar n_{r'}=E_\pi[n_{r'}]=\lambda_{r'}x_{r'}$, for every station $i$ and class $r'$
--   $$\sum_{r\in C_i}I_{rr'}+N_{ir'}=\bar n_{r'}.\qquad(28)$$
--
--   These equalities complement those of Theorem 4.2 in the nonparametric polyhedron, and they are what lets Theorem 4.4 recover the bounds of Theorem 4.1.
--
--   **Formalization Note** $\lambda_{r'}x_{r'}$ is written as the mean number in system $\bar n_{r'}$ (Little's law). The statement uses the shared predicate `Eq28`. The traffic and load hypotheses are retained from the opening of §4, although the busy/idle partition itself does not use them.
-- source:
--   Bertsimas, Paschalidis, Tsitsiklis, Optimization of Multiclass Queueing Networks: Polyhedral and Nonlinear Characterizations of Achievable Performance, MIT Sloan WP #3509-92-MSA (Dec. 1992), p. 20, Theorem 4.3, Eq. (28)

import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Dynamics
import Definitions.Def_MulticlassQNet_FirstOrder_Constraints

namespace MulticlassQNet.FirstOrder

/-- Theorem 4.3 (p. 20): for each station `i` and class `r'`,
`∑_{r ∈ C_i} I_{rr'} + N_{ir'} = λ_{r'} x_{r'}` (= `n̄_{r'}`). -/
theorem theorem_4_3_idle_busy_split {N R : ℕ} (net : Network N R) (lam : Fin R → ℝ)
    (htraffic : net.IsTrafficSolution lam) (hopen : net.IsOpen) (hload : net.LoadLtOne lam)
    (P : Policy net) (π : (Fin R → ℕ) → ℝ) (hA : P.AssumptionA π) :
    net.Eq28 (meanNum π) (P.busyMoment π) (P.idleMoment π) := by sorry

end MulticlassQNet.FirstOrder
