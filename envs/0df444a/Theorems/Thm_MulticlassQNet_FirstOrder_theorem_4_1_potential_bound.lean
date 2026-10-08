-- Prove2me | Theorems.Thm_MulticlassQNet_FirstOrder_theorem_4_1_potential_bound
-- name    : MulticlassQNet.FirstOrder.theorem_4_1_potential_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:36:56.521472+00:00
-- url     : https://prove2.me/theorems/a2ec15a7-603c-49b4-bca2-7959cf631513
-- title:
--   Theorem 4.1 — Σ_{r∈S} λ_r f(r) x_r ≥ N'(S)/D'(S) for every policy satisfying Assumption A
-- statement:
--   Consider an open multiclass queueing network with $N$ single-server stations and $R$ classes: class $r$ is served at station $\sigma(r)$ at exponential rate $\mu_r$, arrives from outside at Poisson rate $\lambda_{0r}$, and after service moves to class $s$ with probability $p_{rs}$ or exits with probability $p_{r0}$. Let $\lambda$ be the solution of the traffic equations (15) and assume $\sum_{r\in C_i}\lambda_r/\mu_r<1$ at every station.
--
--   Let a Markovian sequencing policy satisfy Assumption A, with invariant distribution $\pi$, and let $\bar n_r=E_\pi[n_r]=\lambda_rx_r$, where $x_r$ is the mean response time of class $r$. Let $S$ be any set of classes, and let the f-parameters $f(r)\ge0$ ($r\in S$) and station values $f_i$ satisfy restriction (17). Then
--   $$N'(S)\ \le\ D'(S)\sum_{r\in S}\lambda_r f(r)\,x_r ,$$
--   which, when $D'(S)>0$, is the paper's bound
--   $$\sum_{r\in S}\lambda_rf(r)x_r\ \ge\ \frac{N'(S)}{D'(S)}.\qquad(18)$$
--
--   Each choice of $S$ and $f$ gives a linear inequality on the mean response times that every admissible policy satisfies; minimizing a linear cost over these inequalities bounds the optimal cost of the scheduling problem from below.
--
--   **Formalization Note** The conclusion is stated in product form, $N'(S)\le D'(S)\sum_{r\in S}f(r)\bar n_r$: it is what the proof derives, equals (18) when $D'(S)>0$, and avoids Lean's convention $x/0=0$. The paper's $\lambda_rx_r$ is the mean number $\bar n_r$ (Little's law). Sums over $r'\notin S$ in (17) and $N'(S)$ include the exit $r'=0$ (p. 15). Nonnegativity of $f$ on $S$ is from p. 9 (f-parameters are positive constants). $\lambda$ is an input constrained by (15) and openness.
-- source:
--   Bertsimas, Paschalidis, Tsitsiklis, Optimization of Multiclass Queueing Networks: Polyhedral and Nonlinear Characterizations of Achievable Performance, MIT Sloan WP #3509-92-MSA (Dec. 1992), p. 14, Theorem 4.1, Eqs. (17)–(18)

import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Dynamics
import Definitions.Def_MulticlassQNet_FirstOrder_Constraints

namespace MulticlassQNet.FirstOrder

/-- Theorem 4.1 (p. 14): for any class set `S`, any f-parameters satisfying (17) (and `f ≥ 0`
on `S`, p. 9), and any policy satisfying Assumption A,
`N'(S) ≤ D'(S) · ∑_{r∈S} f(r) λ_r x_r`, i.e. (18) multiplied by `D'(S)`. -/
theorem theorem_4_1_potential_bound {N R : ℕ} (net : Network N R) (lam : Fin R → ℝ)
    (htraffic : net.IsTrafficSolution lam) (hopen : net.IsOpen) (hload : net.LoadLtOne lam)
    (P : Policy net) (π : (Fin R → ℕ) → ℝ) (hA : P.AssumptionA π)
    (S : Finset (Fin R)) (f : Fin R → ℝ) (fi : Fin N → ℝ)
    (h17 : net.FCondition S f fi) (hf : ∀ r ∈ S, 0 ≤ f r) :
    net.Nprime lam S f ≤ net.Dprime S f fi * ∑ r ∈ S, f r * meanNum π r := by sorry

end MulticlassQNet.FirstOrder
