-- Prove2me | Theorems.Thm_MulticlassQNet_FirstOrder_theorem_4_4_nonparametric_dominates
-- name    : MulticlassQNet.FirstOrder.theorem_4_4_nonparametric_dominates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:36:04.233593+00:00
-- url     : https://prove2.me/theorems/5dfb626d-c9df-4d0f-9135-ab6604b349f0
-- title:
--   Theorem 4.4 — nonnegative solutions of (24), (25), (28) satisfy every bound (18) of Theorem 4.1
-- statement:
--   Consider an open multiclass network with external rates $\lambda_{0r}$, routing $p_{rs}$, service rates $\mu_r$, traffic solution $\lambda$ of (15), and the load condition at every station. Let the response-time variables $x_r$, busy moments $I_{rr'}$ and idle moments $N_{ir'}$ be **nonnegative real numbers** satisfying the equalities (24) and (25) of Theorem 4.2 and (28) of Theorem 4.3, with $n_r=\lambda_rx_r$. Then for every set $S$ of classes and every choice of f-parameters $f$ with $f(r)\ge0$ for $r\in S$ and station values $f_i$ satisfying restriction (17),
--   $$N'(S)\ \le\ D'(S)\sum_{r\in S}\lambda_r f(r)\,x_r .$$
--
--   No policy and no probability distribution appear: this is a statement about a polyhedron. It shows that the nonparametric relaxation of Theorems 4.2–4.3 is at least as tight as all the parametric bounds of Theorem 4.1.
--
--   **Formalization Note** The variables are the page's $x_r$, including when $\lambda_r=0$; `Eq24`, `Eq25` and `Eq28` use the derived values $\lambda_rx_r$. The bound is (18) multiplied by $D'(S)$; when $D'(S)>0$ it is (18), and it avoids Lean's convention $x/0=0$. Nonnegativity of $f$ on $S$ comes from p. 9, where f-parameters are introduced as positive constants. Values of $f$ outside $S$ do not enter.
-- source:
--   Bertsimas, Paschalidis, Tsitsiklis, Optimization of Multiclass Queueing Networks: Polyhedral and Nonlinear Characterizations of Achievable Performance, MIT Sloan WP #3509-92-MSA (Dec. 1992), p. 21, Theorem 4.4

import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Constraints

namespace MulticlassQNet.FirstOrder

/-- Theorem 4.4 (p. 21): nonnegative variables `x`, `I`, `Nv` satisfying the
equalities (24), (25) of Theorem 4.2 and (28) of Theorem 4.3 satisfy every inequality (18) of
Theorem 4.1, in product form. -/
theorem theorem_4_4_nonparametric_dominates {N R : ℕ} (net : Network N R) (lam : Fin R → ℝ)
    (htraffic : net.IsTrafficSolution lam) (hopen : net.IsOpen) (hload : net.LoadLtOne lam)
    (x : Fin R → ℝ) (I : Fin R → Fin R → ℝ) (Nv : Fin N → Fin R → ℝ)
    (hx : ∀ r, 0 ≤ x r) (hI : ∀ r r', 0 ≤ I r r') (hNv : ∀ i r', 0 ≤ Nv i r')
    (h24 : net.Eq24 lam (fun r => lam r * x r) I)
    (h25 : net.Eq25 lam (fun r => lam r * x r) I)
    (h28 : net.Eq28 (fun r => lam r * x r) I Nv) :
    ∀ (S : Finset (Fin R)) (f : Fin R → ℝ) (fi : Fin N → ℝ),
      net.FCondition S f fi → (∀ r ∈ S, 0 ≤ f r) →
        net.Nprime lam S f ≤ net.Dprime S f fi * ∑ r ∈ S, f r * (lam r * x r) := by sorry

end MulticlassQNet.FirstOrder
