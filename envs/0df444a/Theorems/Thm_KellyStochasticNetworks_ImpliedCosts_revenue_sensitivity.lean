-- Prove2me | Theorems.Thm_KellyStochasticNetworks_ImpliedCosts_revenue_sensitivity
-- name    : KellyStochasticNetworks.ImpliedCosts.revenue_sensitivity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:48:28.326813+00:00
-- url     : https://prove2.me/theorems/93964d33-e62e-4486-9bd3-b61b98c19e85
-- title:
--   Theorem 4.6 — implied costs and revenue sensitivity
-- statement:
--   Consider a network with finitely many links and routes, nonnegative integer circuit requirements $A_{jr}$, positive offered traffic $\nu_r$, positive integer capacities $C_j$, real values $w_r$ per carried call, and at least one route using each link. Let $B$ be the Erlang fixed point, let $1-L_r=\prod_j(1-B_j)^{A_{jr}}$, $\lambda_r=\nu_r(1-L_r)$, $\rho_j=(1-B_j)^{-1}\sum_rA_{jr}\lambda_r$, and $\delta_j=\rho_j[E(\rho_j,C_j-1)-E(\rho_j,C_j)]$. Define $W(\nu;C)=\sum_rw_r\lambda_r$ through the fixed point; for varying capacity, linearly interpolate the scalar Erlang formula before solving the network equations.
--
--   There is exactly one pair of vectors $s,c$ satisfying
--   $$s_r=w_r-\sum_jc_jA_{jr},\qquad c_j=\delta_j\frac{\sum_rA_{jr}\lambda_r(s_r+c_j)}{\sum_rA_{jr}\lambda_r}.$$
--   The offered-traffic derivatives exist, the left capacity derivatives exist at the integer base capacities, and
--   $$\frac{\partial W}{\partial\nu_r}=(1-L_r)s_r,\qquad \frac{\partial^-W}{\partial C_j}=c_j.$$
--   The selected blocking vector satisfies the published Erlang fixed-point relation with $0\le B_j<1$, and every link has positive carried load.
--
--   The result identifies the marginal value of traffic and capacity with quantities determined by local route-link equations.
--
--   **Formalization Note** Capacity sensitivity is a derivative from the left of a real function, not a finite difference of network revenues and not a derivative on natural numbers. The theorem retains arbitrary integer demands even though the printed proof only handles a $0$–$1$ matrix (finding F2). Positive traffic and positive integer capacities specify the differentiable interior of the original network data. The used-link condition makes the printed quotient in (4.8) meaningful; isolated links are omitted. Zero-traffic marker routes in the proof are not hypotheses or assumed sensitivities. Extending the displayed formula to noninteger base capacities is not asserted (finding F3).
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed p. 103 (PDF p. 111), Theorem 4.6, with definitions on printed p. 102 (PDF p. 110) and proof on printed pp. 103–105 (PDF pp. 111–113); https://doi.org/10.1017/CBO9781139565363

import Definitions.Def_KellyStochasticNetworks_ImpliedCosts_Model

namespace KellyStochasticNetworks.ImpliedCosts

/-- Theorem 4.6. Capacities are positive integers and the capacity derivative is
from the left after linearly interpolating the scalar Erlang formula.
Incidence entries remain arbitrary natural numbers, not just zero or one. -/
theorem revenue_sensitivity {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (w ν : Fin R → ℝ) (C : Fin J → ℕ)
    (hν : ∀ r, 0 < ν r) (hC : ∀ j, 1 ≤ C j)
    (hused : ∀ j, ∃ r, 0 < A j r) :
    let CReal : Fin J → ℝ := fun j => (C j : ℝ)
    let B := blocking A ν CReal
    let lam := carried A ν B
    let δ := improvement A ν C B
    ErlangFixedPoint A ν C B ∧ (∀ j, B j ∈ Set.Ico (0 : ℝ) 1) ∧
    (∀ j, 0 < linkLoad A lam j) ∧
    ∃ sc : (Fin R → ℝ) × (Fin J → ℝ),
      CostSystem A w lam δ sc.1 sc.2 ∧
      (∀ sc' : (Fin R → ℝ) × (Fin J → ℝ),
        CostSystem A w lam δ sc'.1 sc'.2 → sc' = sc) ∧
      (∀ r, HasDerivAt
        (fun x : ℝ => revenue A w (Function.update ν r x) CReal)
        (acceptance A B r * sc.1 r) (ν r)) ∧
      (∀ j, HasDerivWithinAt
        (fun x : ℝ => revenue A w ν (Function.update CReal j x))
        (sc.2 j) (Set.Iic (CReal j)) (CReal j)) := by sorry

end KellyStochasticNetworks.ImpliedCosts
