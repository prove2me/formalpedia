-- Prove2me | Theorems.Thm_NetworkedMarkets_Relaxation_eq_6_revenue_bound
-- name    : NetworkedMarkets.Relaxation.eq_6_revenue_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:58.9001+00:00
-- url     : https://prove2.me/theorems/60e86b3d-154e-4b99-89f2-130e6f1b7b6a
-- title:
--   (6), p. 12 — every competitive equilibrium is feasible for (7) and its revenue is at most h(q^s, q^b)
-- statement:
--   Under the standing assumptions of §2, let $(\gamma,\mu,p,x,q^s,q^b)$ be feasible for the revenue problem (3), i.e. $(\gamma,\mu)\in\Gamma\times\mathcal U$ and $(p,x,q^s,q^b)\in\mathcal X(\gamma,\mu)$. Then $(x,q^s,q^b)$ is feasible for the relaxation (7), and the platform revenue is bounded by
--   $$\sum_{(i,j)\in E}(\gamma^s_i+\gamma^b_j)p_ix_{ij}+\sum_{(i,j)\in E}(\mu^s_i+\mu^b_j)x_{ij}\ \le\ h(q^s,q^b)=\sum_{j\in\mathcal B}F^{-1}_{b_j}\Big(1-\frac{q^b_j}{b_j}\Big)q^b_j-\sum_{i\in\mathcal S}F^{-1}_{s_i}\Big(\frac{q^s_i}{s_i}\Big)q^s_i-\sum_{i\in\mathcal S}c_iq^s_i.$$
--
--   Economically, a type-$j$ buyer pays at most the marginal value $F^{-1}_{b_j}(1-q^b_j/b_j)$ net of the disutility $c_i$, and a type-$i$ seller receives at least the marginal reservation value $F^{-1}_{s_i}(q^s_i/s_i)$; the platform keeps the difference. Together with feasibility for (7), this gives $V_{opt}\le\tilde V_{opt}$ (Step (i-1) of the proof of Theorem 1).
--
--   **Formalization Note.** Feasibility for (7) includes the clause $q^s_i<s_i$ for sellers with unbounded support, which holds in equilibrium because $F_{s_i}<1$ there. The display (6) of p. 12 is proved as (EC.101)–(EC.102) on p. ec39, with the feasibility remark on p. ec40.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), p. 12, (6); EC.3.1, proof of Theorem 1, Step (i-1), (EC.101)–(EC.102), pp. ec39–ec40 (PDF 83–84)

import Mathlib
import Definitions.Def_NetworkedMarkets_Relaxation_Setting

open Filter Topology

namespace NetworkedMarkets.Relaxation

theorem eq_6_revenue_bound {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (hM : M.Standing1)
    (f : Fees S B) (p : S → ℝ) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ)
    (h3 : M.Feas3 f p x qs qb) :
    M.Feas7 x qs qb ∧ M.rev f p x ≤ M.h qs qb := by sorry

end NetworkedMarkets.Relaxation
