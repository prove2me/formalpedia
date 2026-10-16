-- Prove2me | Theorems.Thm_LPCommunity_SBMDense_proposition_11
-- name    : LPCommunity.SBMDense.proposition_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T12:38:28.807853+00:00
-- url     : https://prove2.me/theorems/1d625540-f3db-4cf7-a024-4e32c3a8b2fa
-- title:
--   Proposition 11, p. 28 — a monotone coupling $\mathcal G_{n,q}\subseteq\mathcal G_{n,q,p}\subseteq\mathcal G_{n,p}$
-- statement:
--   Let $0<q\le p<1$ and let $n$ be an even number. Then there is a probability distribution over triples of graphs $(G_1,G_2,G_3)$ on a common node set $V$ of $n$ nodes such that:
--
--   1. the marginal distributions of $G_1$, $G_2$ and $G_3$ are $\mathcal G_{n,q}$, $\mathcal G_{n,q,p}$ and $\mathcal G_{n,p}$, respectively;
--   2. with probability $1$, $G_1$ is a subgraph of $G_2$ and $G_2$ is a subgraph of $G_3$; consequently, for all $i,j\in V$,
--
--   $$
--   \rho_{G_1}(i,j)\ge\rho_{G_2}(i,j)\ge\rho_{G_3}(i,j).
--   $$
--
--   Here $\mathcal G_{n,q,p}$ is the stochastic block model with probability $q$ inside the two communities and $p$ across them. The coupling transfers distance asymptotics of Erdős–Rényi graphs (Propositions 12 and 14) to the stochastic block model (Propositions 16–18).
--
--   **Formalization Note** The distribution is a nonnegative weight on triples of graphs on `Fin n`; its total mass is $1$ because each marginal is a probability law. The marginal of $G_2$ is the law of the graph alone under $\mathcal G_{n,q,p}$, with the planted bisection averaged out. "With probability 1" is "every triple of positive weight". Subgraph is the order on simple graphs on the same node set (every edge of $G_1$ is an edge of $G_2$). Distances are in `ℕ∞`.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 28, Proposition 11

import Mathlib
import Definitions.Def_LPCommunity_LPFail_Setting
import Definitions.Def_LPCommunity_SBMDense_RandomGraphs

open scoped Classical

namespace LPCommunity.SBMDense

theorem proposition_11 (n : ℕ) (p q : ℝ) (hq : 0 < q) (hqp : q ≤ p) (hp : p < 1) (hn : Even n) :
    ∃ w : SimpleGraph (Fin n) × SimpleGraph (Fin n) × SimpleGraph (Fin n) → ℝ,
      (∀ t, 0 ≤ w t) ∧
      (∀ G, ∑ G₂, ∑ G₃, w (G, G₂, G₃) = erWeight n q G) ∧
      (∀ G, ∑ G₁, ∑ G₃, w (G₁, G, G₃) = sbmWeight n q p G) ∧
      (∀ G, ∑ G₁, ∑ G₂, w (G₁, G₂, G) = erWeight n p G) ∧
      ∀ t, w t ≠ 0 → t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧
        ∀ i j, LPCommunity.LPFail.rho t.1 i j ≥ LPCommunity.LPFail.rho t.2.1 i j ∧ LPCommunity.LPFail.rho t.2.1 i j ≥ LPCommunity.LPFail.rho t.2.2 i j := by sorry

end LPCommunity.SBMDense
