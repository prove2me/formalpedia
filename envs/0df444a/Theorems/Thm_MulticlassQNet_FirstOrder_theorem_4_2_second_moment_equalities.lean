-- Prove2me | Theorems.Thm_MulticlassQNet_FirstOrder_theorem_4_2_second_moment_equalities
-- name    : MulticlassQNet.FirstOrder.theorem_4_2_second_moment_equalities
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:36:35.922984+00:00
-- url     : https://prove2.me/theorems/a8d7a10e-8610-4bdd-9d04-748b31cfef09
-- title:
--   Theorem 4.2 — equalities (24), (25) for I_rr' = E[1{B_r} n_r'] and n̄_r = λ_r x_r
-- statement:
--   Consider an open multiclass network with external rates $\lambda_{0r}$, routing $p_{rs}$, service rates $\mu_r$, traffic solution $\lambda$ of (15), and the load condition at every station. For every Markovian sequencing policy satisfying Assumption A with invariant distribution $\pi$, let $\bar n_r=E_\pi[n_r]=\lambda_rx_r$ and $I_{rr'}=E_\pi[1\{B_r\}n_{r'}]$. Then for every class $r$,
--   $$2\mu_rI_{rr}-2\sum_{r'=1}^R\mu_{r'}p_{r'r}I_{r'r}-2\lambda_{0r}\bar n_r=\lambda_{0r}+\lambda_r(1-p_{rr})+\sum_{r'\ne r}\lambda_{r'}p_{r'r},\qquad(24)$$
--   and for all classes $r>r'$,
--   $$\mu_rI_{rr'}+\mu_{r'}I_{r'r}-\sum_{w=1}^R\mu_wp_{wr}I_{wr'}-\sum_{w=1}^R\mu_wp_{wr'}I_{wr}-\lambda_{0r}\bar n_{r'}-\lambda_{0r'}\bar n_r=-\lambda_rp_{rr'}-\lambda_{r'}p_{r'r}.\qquad(25)$$
--
--   These linear equalities in the unknowns $\bar n_r$ and $I_{rr'}$ hold for every admissible policy, so together with nonnegativity they define a polyhedron containing the achievable performance vectors; this is the paper's nonparametric relaxation.
--
--   **Formalization Note** The paper's $\lambda_rx_r$ is the mean number in system $\bar n_r$ (Little's law; the paper uses $n_{r'}=\lambda_{r'}x_{r'}$ on p. 20). The sum over $r'$ in (24) includes $r'=r$. The equalities are stated through the shared predicates `Eq24`, `Eq25`.
-- source:
--   Bertsimas, Paschalidis, Tsitsiklis, Optimization of Multiclass Queueing Networks: Polyhedral and Nonlinear Characterizations of Achievable Performance, MIT Sloan WP #3509-92-MSA (Dec. 1992), p. 18, Theorem 4.2, Eqs. (24)–(25)

import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Dynamics
import Definitions.Def_MulticlassQNet_FirstOrder_Constraints

namespace MulticlassQNet.FirstOrder

/-- Theorem 4.2 (p. 18): for every policy satisfying Assumption A, the moments
`I_{rr'} = E[1{B_r} n_{r'}]` and `n̄_r = λ_r x_r` satisfy (24) and (25). -/
theorem theorem_4_2_second_moment_equalities {N R : ℕ} (net : Network N R) (lam : Fin R → ℝ)
    (htraffic : net.IsTrafficSolution lam) (hopen : net.IsOpen) (hload : net.LoadLtOne lam)
    (P : Policy net) (π : (Fin R → ℕ) → ℝ) (hA : P.AssumptionA π) :
    net.Eq24 lam (meanNum π) (P.busyMoment π) ∧
      net.Eq25 lam (meanNum π) (P.busyMoment π) := by sorry

end MulticlassQNet.FirstOrder
