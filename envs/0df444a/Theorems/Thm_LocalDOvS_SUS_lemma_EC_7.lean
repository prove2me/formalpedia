-- Prove2me | Theorems.Thm_LocalDOvS_SUS_lemma_EC_7
-- name    : LocalDOvS.SUS.lemma_EC_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:24:50.761359+00:00
-- url     : https://prove2.me/theorems/9b8288ce-88d8-44a9-b382-07a3f164204c
-- title:
--   Lemma EC.7, p.ec12 — thinning a convex grid to its odd points loses at most $\epsilon/2$
-- statement:
--   Let $M\ge3$ be an integer, $a\in[0,1]$, and let $h$ be a convex function on $[1,M+a]$. Then:
--
--   1. the restriction $\tilde h$ of $h$ to $[M]$ is discretely convex;
--   2. for every $\epsilon>0$, if
--   $$
--   \max_{x\in[M]}\tilde h(x)-\min_{x\in[M]}\tilde h(x)\le\frac M{20}\,\epsilon, \tag{EC.7}
--   $$
--   then, with $M'=\lceil M/2\rceil$,
--   $$
--   \min_{y\in[M']}\tilde h(2y-1)-\inf_{x\in[1,M+a]}h(x)\le\frac\epsilon2 .
--   $$
--
--   In the proof of Theorem 2 this is the reason a Type-II Operation, which keeps only the odd grid points, still keeps an $\epsilon/2$-optimal decision.
--
--   Differences from the source:
--   - encoding: max_{[M]} h̃ − min_{[M]} h̃ ≤ M/20 · ε → h i − h j ≤ M/20 · ε for all i, j ∈ [M]; reason: equivalent on a finite set
--   - reading: min_{x∈[1,M+a]} h(x) → for every x ∈ [1, M+a], some odd point 2y − 1, y ∈ [M′], has h(2y − 1) ≤ h(x) + ε/2; reason: a convex function on a closed interval need not attain its minimum (it may jump up at an endpoint); the infimum reading is the one that is always defined and it implies the printed inequality whenever the minimum exists
--   - encoding: M′ := ⌈M/2⌉ → (M + 1) / 2 in natural-number division; reason: the same number
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, Lemma EC.7, p.ec12

import Mathlib
import Definitions.Def_LocalDOvS_SUS_DiscConvex

namespace LocalDOvS.SUS

/-- **Lemma EC.7, p.ec12** (Zhang–Zheng–Lavaei, arXiv:2012.02427v2). Let `h` be convex on
`[1, M + a]` with integer `M ≥ 3` and `a ∈ [0, 1]`. Then the restriction `h̃` of `h` to `[M]` is
(discretely) convex. Furthermore, for `ε > 0`, if `max_{[M]} h̃ − min_{[M]} h̃ ≤ M/20 · ε`
(EC.7), then `min_{y ∈ [M']} h̃(2y − 1) − min_{x ∈ [1, M + a]} h(x) ≤ ε/2`, `M' := ⌈M/2⌉`.

**Formalization Note.** (EC.7) is written `h i − h j ≤ M/20 · ε` for all `i, j ∈ [M]`. The
conclusion is written "some odd grid point `2y − 1`, `y ∈ [M']`, satisfies
`h(2y − 1) ≤ h(x) + ε/2` for every `x ∈ [1, M + a]`", which is the printed inequality whenever
the minimum over `[1, M + a]` exists, and avoids a real infimum; no continuity is added.
`⌈M/2⌉ = (M + 1)/2` in natural-number division. -/
theorem lemma_EC_7 (h : ℝ → ℝ) (M : ℕ) (a : ℝ) (hM : 3 ≤ M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hconv : ConvexOn ℝ (Set.Icc (1 : ℝ) (M + a)) h) :
    DiscConvex M (fun n => h n) ∧
    ∀ ε : ℝ, 0 < ε →
      (∀ i ∈ Finset.Icc 1 M, ∀ j ∈ Finset.Icc 1 M, h i - h j ≤ (M : ℝ) / 20 * ε) →
      ∃ y ∈ Finset.Icc 1 ((M + 1) / 2), ∀ x ∈ Set.Icc (1 : ℝ) (M + a),
        h ((2 * y - 1 : ℕ) : ℝ) ≤ h x + ε / 2 := by sorry

end LocalDOvS.SUS
