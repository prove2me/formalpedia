-- Prove2me | Theorems.Thm_NetworkedMarkets_Relaxation_proposition_EC_1_i
-- name    : NetworkedMarkets.Relaxation.proposition_EC_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:02.389985+00:00
-- url     : https://prove2.me/theorems/447e3bc2-4551-4372-b5a2-75bdad986322
-- title:
--   Proposition EC.1(i), p. ec3 (PDF 47), at problem (7) — the relaxation (7) has an optimal solution
-- statement:
--   Under the standing assumptions and Assumptions 1–2, the convex program (7),
--   $$\max_{x,q^s,q^b}\ h(q^s,q^b)\quad\text{s.t.}\quad \sum_{i:(i,j)\in E}x_{ij}=q^b_j,\ \ q^s_i=\sum_{j:(i,j)\in E}x_{ij},\ \ q^b_j\le b_j,\ \ q^s_i\le s_i,\ \ x_{ij}\ge 0\ \ ((i,j)\in E),$$
--   has an optimal solution $(\bar x,\bar q^s,\bar q^b)$.
--
--   This guarantees that the hypothesis of Theorem 1 ("let $(\bar x,\bar q^s,\bar q^b)$ denote an optimal solution to (7)") can be met.
--
--   **Formalization Note.** This is Proposition EC.1(i) at the instance of Lemma EC.1(ii) ($g_j(q)=F^{-1}_{b_j}(1-q/b_j)q$, $h_i(q)=F^{-1}_{s_i}(q/s_i)q$, $w_{ij}=c_i$); the general framework problem (EC.1) is not formalized. For sellers with unbounded support the feasible set also requires $q^s_i<s_i$, where the paper's objective is $-\infty$ otherwise; the feasible set is then not closed, and the existence of a maximizer is part of the content.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), p. ec3 (PDF 47), Proposition EC.1(i), at the instance of Lemma EC.1(ii), p. ec4 (PDF 48)

import Mathlib
import Definitions.Def_NetworkedMarkets_Relaxation_Setting

open Filter Topology

namespace NetworkedMarkets.Relaxation

theorem proposition_EC_1_i {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (hM : M.Standing) :
    ∃ (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ), M.IsOpt7 x qs qb := by sorry

end NetworkedMarkets.Relaxation
