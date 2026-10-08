-- Prove2me | Theorems.Thm_FriendlyShadow_Gaussian_lemma_21
-- name    : FriendlyShadow.Gaussian.lemma_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:17:34.21063+00:00
-- url     : https://prove2.me/theorems/c8a0e2ac-d018-4703-a5be-b1dcc6f0c63d
-- title:
--   Lemma 21, p. 21 — an L-log-Lipschitz density on ℝᵈ, d ≥ 3, has L·R(1/2) ≥ d/3
-- statement:
--   Let $d\ge3$ and let $\mu$ be a probability density on $\mathbb R^d$ with mean $y$ that is $L$-log-Lipschitz (Definition 15). If its cutoff radius $R(1/2)$ (Definition 18) is at most $R$, that is $\Pr_{X\sim\mu}[\|X-y\|\ge R]\le 1/2$, then
--   $$L\,R\ \ge\ \frac d3 .$$
--
--   A density cannot be both very concentrated (small cutoff radius) and very flat (small log-Lipschitz constant). The lemma quantifies this trade-off, and the proof of Lemma 39 uses it.
--
--   **Formalization Note** The paper states $L\,R(1/2)\ge d/3$ for the cutoff radius itself. Here $R$ is any upper bound of $R(1/2)$, which gives the same statement because $L>0$ for every log-Lipschitz probability density.
-- source:
--   Dadush & Huiberts, arXiv:1711.05667v4, Lemma 21, p. 21 (parameters of Defs 15 and 18, p. 20)

import Mathlib
import Definitions.Def_FriendlyShadow_Gaussian_Model

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace FriendlyShadow.Gaussian

/-- Lemma 21 (p. 21). For a probability density `μ` on `ℝᵈ`, `d ≥ 3`, with mean `y`, which is
`L`-log-Lipschitz and whose cutoff radius `R(1/2)` is at most `R`, we have `L·R ≥ d/3`. -/
theorem lemma_21 {d : ℕ} (hd : 3 ≤ d) (μ : EuclideanSpace ℝ (Fin d) → ℝ) (hμ : IsDensity μ)
    (y : EuclideanSpace ℝ (Fin d)) (hy : HasMean μ y) (L : ℝ) (hL : LogLipschitz μ L)
    (R : ℝ) (hR : CutoffRadiusLE μ y (1 / 2) R) :
    (d : ℝ) / 3 ≤ L * R := by sorry

end FriendlyShadow.Gaussian
