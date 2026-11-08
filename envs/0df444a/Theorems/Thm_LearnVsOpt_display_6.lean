-- Prove2me | Theorems.Thm_LearnVsOpt_display_6
-- name    : LearnVsOpt.display_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:01:18.59543+00:00
-- url     : https://prove2.me/theorems/47409ae1-9545-4037-a6a0-7091350d4d10
-- title:
--   (6), p.9 — the inner product of step-function sums on $L^2([-1,1])$
-- statement:
--   Let $r=\sum_k w_k\mathbb 1_{\cdot\le q_k}$ and $\tilde r=\sum_\ell\tilde w_\ell\mathbb 1_{\cdot\le\tilde q_\ell}$ be finite linear combinations of step functions, with real weights and with thresholds $q_k,\tilde q_\ell\in[0,1]$. Then the inner product $\langle g,\tilde g\rangle=\int_{-1}^1 g(x)\tilde g(x)\,dx$ evaluates as
--   $$
--   \langle r,\tilde r\rangle=\sum_{k,\ell}w_k\tilde w_\ell\big(1+\min\{q_k,\tilde q_\ell\}\big),\qquad \|r\|_{L^2}^2=\sum_{k,k'}w_kw_{k'}\big(1+\min\{q_k,q_{k'}\}\big).
--   $$
--   This is what makes the calibration error computable: the program's arithmetic on $R_t$ is this formula.
--
--   Differences from the source:
--   - encoding: finite index sets of k, ℓ → Fin m, Fin m′; reason: relabeling
-- source:
--   Fikioris, Sivan & Tardos, Learning vs. Optimizing Players in Budgeted Games, arXiv:2611.05580, (6), p.9

import Mathlib

namespace LearnVsOpt

/-- **Display (6)** (Fikioris, Sivan & Tardos, *Learning vs. Optimizing Players in Budgeted Games*,
arXiv:2611.05580, (6), p.9). For linear combinations of step functions `r = Σ_k w_k 1_{·≤q_k}` and
`r̃ = Σ_ℓ w̃_ℓ 1_{·≤q̃_ℓ}` with thresholds in `[0, 1]`, the inner product (5) on `L²([−1, 1])` is
`⟨r, r̃⟩ = Σ_{k,ℓ} w_k w̃_ℓ (1 + min{q_k, q̃_ℓ})`, and `‖r‖²_{L²} = Σ_{k,k'} w_k w_{k'} (1 + min{q_k, q_{k'}})`.
-/
theorem display_6 {m m' : ℕ} (w q : Fin m → ℝ) (w' q' : Fin m' → ℝ)
    (hq : ∀ k, q k ∈ Set.Icc (0 : ℝ) 1) (hq' : ∀ l, q' l ∈ Set.Icc (0 : ℝ) 1) :
    (∫ y in (-1 : ℝ)..1, (∑ k, w k * (if y ≤ q k then 1 else 0)) *
        (∑ l, w' l * (if y ≤ q' l then 1 else 0))) =
      ∑ k, ∑ l, w k * w' l * (1 + min (q k) (q' l)) ∧
    (∫ y in (-1 : ℝ)..1, (∑ k, w k * (if y ≤ q k then 1 else 0)) ^ 2) =
      ∑ k, ∑ k', w k * w k' * (1 + min (q k) (q k')) := by sorry

end LearnVsOpt
