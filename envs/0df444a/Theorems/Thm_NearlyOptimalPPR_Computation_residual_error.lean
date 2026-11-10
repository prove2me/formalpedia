-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_residual_error
-- name    : NearlyOptimalPPR.Computation.residual_error
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:35:26.605085+00:00
-- url     : https://prove2.me/theorems/96da7ef4-b3b9-4591-9a42-65edc01be0ef
-- title:
--   Lemma 2.2 — Residual and approximation error
-- statement:
--   Let $G=(V,E)$ be a finite simple unweighted undirected graph, let $s$ be a nonisolated seed, and let $0<\alpha<1$, $0<\varepsilon\le1$. Let $A,D,M=D-(1-\alpha)A$ have their usual graph meanings. For every nonnegative potential $z:V\to\mathbb R$, set $\widehat\pi_s=\alpha Dz$. On the positive-degree vertices, with extension by zero at the others,
--
--   $$\pi_s-\widehat\pi_s=\alpha DM^{-1}(e_s-Mz).$$
--
--   In particular,
--
--   $$0\le e_s-Mz\le\varepsilon d\quad\Longrightarrow\quad |\widehat\pi_s(v)-\pi_s(v)|\le\varepsilon d_v\quad(v\in V).$$
--
--   All vector inequalities are coordinatewise. The graph may be disconnected and may contain isolated vertices other than the seed. Values of $z$ at those vertices do not affect either side of the identity.
--
--   This transfers a residual bound for the actual potential to the absolute ACL guarantee without adding a residual representation to the definition of accuracy.
--
--   Differences from the source:
--   - encoding: matrix identities understood on positive-degree vertices with zero output elsewhere → the positive-degree Green operator and the shared PageRank wrapper; reason: the full graph matrix may be singular but its inverse default is never used
-- source:
--   Rong-Hua Li, Quanqing Xu, Yichun Yang, Junjie Zhou, STOC 2027 submission #884 (October 2026), Lemma 2.2 and standing matrix/parameter conventions p.4

import Mathlib
import Definitions.Def_NearlyOptimalPPR_Computation_model

set_option autoImplicit false

open Finset Matrix

namespace NearlyOptimalPPR.Computation

/-- Li, Xu, Yang, Zhou, STOC 2027 submission #884 (October 2026),
Lemma 2.2 p.4, including its standing nonisolated-source convention. -/
theorem residual_error {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (α ε : ℝ)
    (hα : 0 < α ∧ α < 1) (hε : 0 < ε ∧ ε ≤ 1) (hs : 0 < G.degree s)
    (z : V → ℝ) (hz : ∀ v, 0 ≤ z v) :
    ppr G α s - potentialOutput G α z =
        potentialOutput G α (green G α (residual G α s z)) ∧
      ((∀ v, 0 ≤ residual G α s z v ∧ residual G α s z v ≤ ε * LocalPush.deg G v) →
        ACL G α ε s (potentialOutput G α z)) := by sorry

end NearlyOptimalPPR.Computation
