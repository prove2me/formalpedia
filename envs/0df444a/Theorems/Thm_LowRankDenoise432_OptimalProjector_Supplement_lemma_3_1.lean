-- Prove2me | Theorems.Thm_LowRankDenoise432_OptimalProjector_Supplement_lemma_3_1
-- name    : LowRankDenoise432.OptimalProjector.Supplement.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:40:48.030053+00:00
-- url     : https://prove2.me/theorems/d33f9af3-0f15-4df4-bcff-fd21ea5be3ed
-- title:
--   Lemma 3.1 — estimation error bounds shortest-path regret; regret is zero below half the margin
-- statement:
--   Let $\mathcal Z\subseteq\{0,1\}^d$ be a nonempty finite family of paths, each with at most $L$ edges. Let $c,\hat c\in\mathbb R^d$ be arbitrary cost vectors, and let
--   $$\hat z\in\arg\min_{z\in\mathcal Z}\hat c^\top z,\qquad z^*\in\arg\min_{z\in\mathcal Z}c^\top z$$
--   be any minimizers (ties are allowed). Then
--   $$c^\top\hat z-c^\top z^*\;\le\;(\hat c-c)^\top(z^*-\hat z)\;\le\;2L\,\|\hat c-c\|_\infty .$$
--   Moreover, if $\|\hat c-c\|_\infty<\Delta(c)/(2L)$, where $\Delta(c)$ is the smallest cost difference between the optimum and a path that is not optimal, then the regret $c^\top\hat z-c^\top z^*$ is zero. If every path is optimal for $c$, the regret is zero with no condition.
--
--   The lemma turns any error bound on the estimated cost vector into a bound on the regret of the decision, and is the deterministic step behind the suboptimality probability of Theorem 3.6.
--
--   **Formalization Note.** $\|v\|_\infty=\max_e|v_e|$ is the published `linfNorm`. The zero-regret condition is written $2L\|\hat c-c\|_\infty<\Delta(c)$ and is required only when some path is not optimal.
--
--   Differences from the source:
--   - generalization: 𝒵 the set of source-to-sink paths of a DAG with at most L edges each → any nonempty finite family of 0/1 vectors with at most L ones each; reason: the proof uses only these properties, and every path set of a DAG is such a family
--   - encoding: ‖ĉ − c‖∞ < Δ/(2L) → 2L‖ĉ − c‖∞ < Δ(c), assumed only when some path is not optimal; reason: when a non-optimal path exists L ≥ 1, so the two are equivalent; when none exists Δ is undefined in the source and the regret is zero anyway
-- source:
--   Henry Aldridge-Krawciw, Irene Aldridge, Low-Rank Denoising for Predict-then-Optimize, STOC 2027 submission #432 (October 2026), source.pdf SHA-256 8d92579f841e1b4853ee9eecd477b739374858db635a23defcc3fb767b137889, PDF p.2, Lemma 3.1 (Section 3.1); setting PDF p.1 Section 1.1 and PDF p.2 Section 2 (Δ(c)); proof PDF pp.5–6

import Mathlib
import Definitions.Def_HighDimStat_SparseLinear_LInftyNorm
import Definitions.Def_LowRankDenoise432_OptimalProjector_Supplement_Regret
open Matrix HighDimStat.SparseLinear

namespace LowRankDenoise432.OptimalProjector.Supplement

/-- Lemma 3.1 (PDF p.2; proof PDF pp.5–6). Let `𝒵` be a nonempty finite family of `0/1` vectors
with at most `L` ones each, `ĉ, c` arbitrary cost vectors, `ẑ ∈ argmin_{z∈𝒵} ĉᵀz` and
`z* ∈ argmin_{z∈𝒵} cᵀz` (any minimizers). Then
`cᵀẑ − cᵀz* ≤ (ĉ − c)ᵀ(z* − ẑ) ≤ 2L‖ĉ − c‖∞`, and if `2L‖ĉ − c‖∞ < Δ(c)` (required only when some
path is not optimal for `c`), the regret `cᵀẑ − cᵀz*` is zero. -/
theorem lemma_3_1 {d L : ℕ} (Z : Finset (Fin d → ℝ)) (hZ : IsPathFamily Z L)
    (c chat zhat zstar : Fin d → ℝ)
    (hzhat : IsOptimalPath Z chat zhat) (hzstar : IsOptimalPath Z c zstar) :
    c ⬝ᵥ zhat - c ⬝ᵥ zstar ≤ (chat - c) ⬝ᵥ (zstar - zhat) ∧
      (chat - c) ⬝ᵥ (zstar - zhat) ≤ 2 * (L : ℝ) * linfNorm (chat - c) ∧
      ((HasNonoptimal Z c → 2 * (L : ℝ) * linfNorm (chat - c) < pathGap Z c) →
        c ⬝ᵥ zhat - c ⬝ᵥ zstar = 0) := by sorry

end LowRankDenoise432.OptimalProjector.Supplement
