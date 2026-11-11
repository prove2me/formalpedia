-- Prove2me | Theorems.Thm_OptimalLCA_Matching_lemma_5_9
-- name    : OptimalLCA.Matching.lemma_5_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:47:58.298198+00:00
-- url     : https://prove2.me/theorems/3b1eda58-0480-4842-b0b5-b4fecabddd7d
-- title:
--   Lemma 5.9 — bounded scores, oscillation ≤ 5/18, ratios in [e⁻¹, e]
-- statement:
--   Let $G$ have maximum degree at most $\Delta\ge2$. For every round $t$ of Algorithm 2:
--   (a) every coordinate of the scores satisfies $|a|,|\hat s|<\tfrac1{24}$, hence $|\tfrac32a-\hat s|<\tfrac5{48}$, and the gradient-stage score lies in $(-\tfrac16,\tfrac18)$;
--   (b) $\operatorname{osc}(\log\rho_t)\le\tfrac5{18}$, where $\rho_t=\bar q_t/q_t$ and $\operatorname{osc}(c)=\max_u(\max_{a\in I_u}c_{ua}-\min_{a\in I_u}c_{ua})$;
--   (c) every coordinate of $\bar q_t/q_t$, $q'_t/q_t$, $q_{t+1}/q_t$, $\bar q_{t+1}/\bar q_t$ lies in $[e^{-1},e]$, and so does the corresponding load ratio $\ell_v(\cdot)/\ell_v(\cdot)$ at every nonisolated vertex $v$.
--   These bounds let the sampler of §6 use constant-bias coins.
--
--   Differences from the source:
--   - encoding: osc(log ρ_t) ≤ 5/18 → log ρ_i − log ρ_j ≤ 5/18 for all coordinates i, j of one block; reason: equivalent to the max over blocks of max − min
--   - encoding: scores (p. 27) on real coordinates, vanishing on dummies → the score vectors computed in Algorithm 3, on all coordinates; reason: on a real coordinate they are the p. 27 formulas; on a dummy they are 0
--   - encoding: state restricted to nonisolated vertices → Algorithm 2 run on all vertices (isolated blocks are dummy-only); reason: the coordinates of nonisolated vertices are unchanged; isolated coordinates have ratio 1 and score 0
--   - encoding: a graph with vertex set [n] → any finite vertex type V with a SimpleGraph (decidable adjacency); reason: relabelling; every graph on [n] is an instance
-- source:
--   Cohen, Roghani, Optimal LCA and Sublinear Estimation for Bipartite Matching in Δ^O(1/ε) Queries, arXiv:2611.06024 (version not printed; PDF sha256 5a43ec12…3eb3), p. 28, Lemma 5.9

import Mathlib
import Definitions.Def_OptimalLCA_Matching_SaddlePoint
import Definitions.Def_OptimalLCA_Matching_Optimizer

namespace OptimalLCA.Matching

/-- Lemma 5.9 (bounded tilts). For every round `t` of Algorithm 2:
(a) every coordinate of the scores satisfies `|a|, |ŝ| < 1/24`, hence `|3/2 a - ŝ| < 5/48`,
and the gradient-stage score lies in `(-1/6, 1/8)`;
(b) `osc(log ρ_t) ≤ 5/18` with `ρ_t = q̄_t / q_t`;
(c) every coordinate of `q̄_t/q_t`, `q'_t/q_t`, `q_{t+1}/q_t`, `q̄_{t+1}/q̄_t` lies in
`[e⁻¹, e]`, and so does the corresponding load ratio at every nonisolated vertex. -/
theorem lemma_5_9 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Δ : ℕ) (hΔ : 2 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) (t : ℕ) :
    (∀ i : Idx G,
      |(optRound G Δ t).scoreA i| < 1 / 24 ∧ |(optRound G Δ t).scoreS i| < 1 / 24 ∧
      |3 / 2 * (optRound G Δ t).scoreA i - (optRound G Δ t).scoreS i| < 5 / 48 ∧
      (optRound G Δ t).gradScore i ∈ Set.Ioo (-1 / 6 : ℝ) (1 / 8)) ∧
    (∀ i j : Idx G, owner i = owner j →
      Real.log ((optState G Δ t).qbar i / (optState G Δ t).q i) -
        Real.log ((optState G Δ t).qbar j / (optState G Δ t).q j) ≤ 5 / 18) ∧
    (∀ i : Idx G,
      (optState G Δ t).qbar i / (optState G Δ t).q i ∈
          Set.Icc (Real.exp (-1)) (Real.exp 1) ∧
      (optRound G Δ t).qPrime i / (optState G Δ t).q i ∈
          Set.Icc (Real.exp (-1)) (Real.exp 1) ∧
      (optState G Δ (t + 1)).q i / (optState G Δ t).q i ∈
          Set.Icc (Real.exp (-1)) (Real.exp 1) ∧
      (optState G Δ (t + 1)).qbar i / (optState G Δ t).qbar i ∈
          Set.Icc (Real.exp (-1)) (Real.exp 1)) ∧
    (∀ v : V, 0 < G.degree v →
      load G (optState G Δ t).qbar v / load G (optState G Δ t).q v ∈
          Set.Icc (Real.exp (-1)) (Real.exp 1) ∧
      load G (optRound G Δ t).qPrime v / load G (optState G Δ t).q v ∈
          Set.Icc (Real.exp (-1)) (Real.exp 1) ∧
      load G (optState G Δ (t + 1)).q v / load G (optState G Δ t).q v ∈
          Set.Icc (Real.exp (-1)) (Real.exp 1) ∧
      load G (optState G Δ (t + 1)).qbar v / load G (optState G Δ t).qbar v ∈
          Set.Icc (Real.exp (-1)) (Real.exp 1)) := by sorry

end OptimalLCA.Matching
