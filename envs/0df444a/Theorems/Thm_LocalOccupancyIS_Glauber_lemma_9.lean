-- Prove2me | Theorems.Thm_LocalOccupancyIS_Glauber_lemma_9
-- name    : LocalOccupancyIS.Glauber.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:58:11.329295+00:00
-- url     : https://prove2.me/theorems/24b63c5a-0020-4b5c-b796-2725e5aad057
-- title:
--   Lemma 9 — two-sweep empty-set and occupancy estimates
-- statement:
--   Let $F$ be a finite simple graph with $k$ vertices and average degree at most the real number $a$. At fugacity $\lambda>0$, start from any independent set and apply two full sweeps in arbitrary deterministic orders, which may differ. Write $Y$ for the resulting set and $p=\lambda/(1+\lambda)$. Then
--
--   $$\mathbb P(Y=\varnothing)\ge(1+\lambda)^{-k},\qquad
--   \mathbb E|Y|\ge p\sum_v(1+\lambda)^{-d_F(v)}\ge pk(1+\lambda)^{-a}.$$
--
--   The graph may be empty; its independent-set space has one state. These finite-time endpoint estimates apply without an equilibrium or mixing assumption and supply the small-available-graph estimates for the certificate.
--
--   Differences from the source:
--   - encoding: finite independent sets and induced subgraphs → Boolean configurations on finite types and induced subtypes; reason: these presentations preserve all feasible configurations, including the empty one
-- source:
--   Ewan Davies, Brian Tan, STOC 2027 submission #982 (October 2026), Lemma 9, p. 16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/982.pdf#page=16

import Definitions.Def_LocalOccupancyIS_Glauber_Dynamics

open scoped BigOperators

namespace LocalOccupancyIS.Glauber
/-- Lemma 9, p.16. The empty graph is included. -/
theorem lemma_9 {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (a lam : ℝ) (hlam : 0 < lam)
    (ha : avgDegree F ≤ a) (w₁ w₂ : List V)
    (h₁ : IsSweep Finset.univ w₁) (h₂ : IsSweep Finset.univ w₂) (I : State F) :
    let ν := push (point I) (word F lam (w₁ ++ w₂))
    expectation ν (fun σ => if size σ.val = 0 then 1 else 0) ≥ (1 + lam) ^ (-(Fintype.card V : ℝ)) ∧
    expectation ν (fun σ => size σ.val) ≥ p lam * ∑ v, (1 + lam) ^ (-(F.degree v : ℝ)) ∧
    p lam * (∑ v, (1 + lam) ^ (-(F.degree v : ℝ))) ≥
      p lam * Fintype.card V * (1 + lam) ^ (-a) := by sorry
end LocalOccupancyIS.Glauber
