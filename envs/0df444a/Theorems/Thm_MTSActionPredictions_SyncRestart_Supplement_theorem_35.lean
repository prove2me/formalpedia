-- Prove2me | Theorems.Thm_MTSActionPredictions_SyncRestart_Supplement_theorem_35
-- name    : MTSActionPredictions.SyncRestart.Supplement.theorem_35
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:31:12.77681+00:00
-- url     : https://prove2.me/theorems/dcecd89f-ecc0-481f-a450-f6ac4db0186a
-- title:
--   Theorem 35 — greedy projection is strictly $\sqrt T$-competitive for Euclidean convex body chasing
-- statement:
--   Let $d\ge0$, $x_0\in\mathbb R^d$ and let $K_1,\dots,K_T\subseteq\mathbb R^d$ be nonempty closed convex sets. The greedy algorithm Project moves to $x_t=\operatorname{proj}_{K_t}(x_{t-1})$, the closest point of $K_t$ to $x_{t-1}$. For every feasible offline solution $y_0=x_0,y_1,\dots,y_T$ with $y_t\in K_t$,
--   $$\sum_{t=1}^T\|x_t-x_{t-1}\|_2\le\sqrt T\cdot\sum_{t=1}^T\|y_t-y_{t-1}\|_2 .$$
--
--   The coefficient is exactly $\sqrt T$, without an additive term. This is the short-sequence guarantee to which the synchronized restart of Theorem 6 is applied in the proof of Theorem 4.
--
--   Differences from the source:
--   - encoding: OFF (the proof uses an optimal offline path) → every feasible offline path y with y_0 = x_0 and y_t ∈ K_t; reason: the paper’s strict competitiveness is against every offline solution; the proof works for any feasible path
--   - encoding: requests K_1, …, K_T and positions in R^d → a list of bodies in EuclideanSpace ℝ (Fin d); real-valued movement costs; reason: same instances
--   - encoding: R^d with d ≥ 1 → every d : ℕ, including d = 0; reason: R^0 is a single point, where every cost is 0 and the bound holds trivially; no instance with d ≥ 1 changes
-- source:
--   Júlia Baligács, Christian Coester, Alexa Tudose, STOC 2027 submission #1248 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1248.pdf; Theorem 35, PDF p. 24 / printed p. 23, with Project defined on the same page

import Definitions.Def_MTSActionPredictions_SyncRestart_Supplement_ConvexChasing

open CBCLowerBound.EveryNorm

namespace MTSActionPredictions.SyncRestart.Supplement

/-- Theorem 35, PDF 24 / printed 23: the greedy projection algorithm `Project` is strictly
`√T`-competitive on every request sequence of length `T`, against every feasible offline solution
from the same start, in every dimension `d`. -/
theorem theorem_35 (d : ℕ) (x₀ : EuclideanSpace ℝ (Fin d))
    (σ : List (Set (EuclideanSpace ℝ (Fin d)))) (hσ : ∀ K ∈ σ, IsBody K)
    (y : ℕ → EuclideanSpace ℝ (Fin d)) (hy : FeasiblePath x₀ σ y) :
    (project d x₀).cost σ ≤ Real.sqrt σ.length * pathCost σ.length y := by sorry

end MTSActionPredictions.SyncRestart.Supplement
