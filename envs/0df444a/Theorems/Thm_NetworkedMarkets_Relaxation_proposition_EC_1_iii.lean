-- Prove2me | Theorems.Thm_NetworkedMarkets_Relaxation_proposition_EC_1_iii
-- name    : NetworkedMarkets.Relaxation.proposition_EC_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:32.835575+00:00
-- url     : https://prove2.me/theorems/dadb99a0-7dbd-4fe5-8887-f8a7a4a9fe2d
-- title:
--   Proposition EC.1(iii), p. ec3 (PDF 47), at problem (7) — at every optimum of (7) the slopes are finite and KKT multipliers (EC.3) exist
-- statement:
--   Under the standing assumptions and Assumptions 1–2, let $(x,q^s,q^b)$ be an optimal solution of (7), and let $g_j(q)=F^{-1}_{b_j}(1-q/b_j)q$, $h_i(q)=F^{-1}_{s_i}(q/s_i)q$. Then the slopes $g'_j(q^b_j)$ and $h'_i(q^s_i)$ are finite, and there are multipliers $\theta^b,\eta^b\in\mathbb R^{\mathcal B}$, $\theta^s,\eta^s\in\mathbb R^{\mathcal S}$, $\pi\in\mathbb R^{E}$ with
--   $$\begin{aligned}
--   &g'_j(q^b_j)-\theta^b_j-\eta^b_j=0, && h'_i(q^s_i)-\theta^s_i+\eta^s_i=0, && \theta^b_j-\theta^s_i+\pi_{ij}-c_i=0\ \ ((i,j)\in E),\\
--   &q^b_j\le b_j\ \perp\ \eta^b_j\ge 0, && q^s_i\le s_i\ \perp\ \eta^s_i\ge0, && x_{ij}\ge0\ \perp\ \pi_{ij}\ge0\ \ ((i,j)\in E),
--   \end{aligned}$$
--   together with the flow equations $\sum_{i:(i,j)\in E}x_{ij}=q^b_j$, $\sum_{j:(i,j)\in E}x_{ij}=q^s_i$. Here $u\perp v$ means both inequalities hold and $uv=0$ for the corresponding slack.
--
--   These are the Karush–Kuhn–Tucker conditions (EC.3) in derivative form. The multipliers $\theta^s$ become the prices, and $\theta^b$ the buyers' effective costs, in the subscription-only implementation of Step (i-2).
--
--   **Formalization Note.** Instance of Proposition EC.1(iii) at Lemma EC.1(ii) ($w_{ij}=c_i$); the framework problem (EC.1) is not formalized. The slope $g'_j(q)$ is the limit of the derivative of $g_j$ as the argument tends to $q$ inside $(0,b_j)$, which is the derivative at interior points and footnote 22's one-sided convention at $0$ and $b_j$; asserting that this limit equals a real number is the finiteness claim. The converse sentence of Proposition EC.1(iii) (every pair satisfying (EC.3) is optimal) is not posed.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), p. ec3 (PDF 47), Proposition EC.1(iii), (EC.3a)–(EC.3h), at the instance of Lemma EC.1(ii), p. ec4 (PDF 48)

import Mathlib
import Definitions.Def_NetworkedMarkets_Relaxation_Setting

open Filter Topology

namespace NetworkedMarkets.Relaxation

theorem proposition_EC_1_iii {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (hM : M.Standing)
    (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ) (hopt : M.IsOpt7 x qs qb) :
    ∃ (θb : B → ℝ) (θs : S → ℝ) (ηb : B → ℝ) (ηs : S → ℝ) (π : S → B → ℝ),
      M.IsSpecialDual x qs qb θb θs ηb ηs π := by sorry

end NetworkedMarkets.Relaxation
