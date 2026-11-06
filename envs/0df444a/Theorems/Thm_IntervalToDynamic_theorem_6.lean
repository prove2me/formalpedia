-- Prove2me | Theorems.Thm_IntervalToDynamic_theorem_6
-- name    : IntervalToDynamic.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:22:07.399114+00:00
-- url     : https://prove2.me/theorems/2ba6f3d1-1f4d-434a-9e71-ea8d113f71dc
-- title:
--   Theorem 6 — improper interval comparators on at most two pieces
-- statement:
--   Let $D_{\mathcal X}>0$ and $\mathcal Y=\mathcal B(D_{\mathcal X})$. For $t\in[n]$ let $u_t\in\mathcal B(D_{\mathcal X}/2)$, and write $P_{[n]}=\sum_{t=2}^n\|u_t-u_{t-1}\|_2$. In each case below there is a partition of $[n]$ into $1\le S\le2$ nonempty consecutive pieces $I_s$ and an interval comparator $z_s\in\mathcal Y$ on each piece. Writing $\text{Err}_{[n]}=\sum_{s=1}^S\text{Err}_{I_s}(z_s)$:
--
--   1. If every $h_t(y)=d_t^\top y$ is linear and $P_{[n]}\le D_{\mathcal X}/2$, then $\text{Err}_{[n]}\le0$.
--   2. If every $h_t:\mathcal Y\to\mathbb R$ is differentiable and $H$-smooth for $H>0$, and $c_t=u_t-H^{-1}\nabla h_t(u_t)\in\mathcal Y$, then
--   $$
--   \text{Err}_{[n]}\le\frac{H\,P_{[n]}^2\,n}8 .
--   $$
--
--   Comparators outside $\mathcal X$ thus offset the error of replacing a moving comparator by a fixed one.
--
--   Differences from the source:
--   - encoding: h_t : Y → ℝ differentiable, with gradient ∇h_t → a gradient oracle `gh t` with `HasGradientWithinAt` on Y; reason: h_t lives on Y only; Y has nonempty interior, so the oracle is the gradient
--   - encoding: partition of [n] into 1 ≤ S ≤ 2 nonempty consecutive pieces → `TwoPieceComparators`: the piece [1, n], or [1, m] and [m + 1, n] with 1 ≤ m < n; reason: the only such partitions
--   - encoding: [n], n a positive integer → `1 ≤ n`; reason: [n] is nonempty on the page
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Theorem 6, p.10

import Mathlib
import Definitions.Def_IntervalToDynamic_TwoPieceComparators
import Definitions.Def_IntervalToDynamic_IsSmoothOn
import Definitions.Def_IntervalToDynamic_pathLengthOn

namespace IntervalToDynamic

/-- Theorem 6 (improper interval comparators). Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Theorem 6, p.10.

Let `D_X > 0`, `Y = B(D_X)`, `u_t ∈ B(D_X/2)` for `t ∈ [n]`, and `P_[n] = ∑_{t=2}^n ‖u_t − u_{t−1}‖₂`.
In each case there is a partition of `[n]` into `1 ≤ S ≤ 2` nonempty consecutive pieces `I_s` and
comparators `z_s ∈ Y` such that, with `Err_[n] = ∑_s Err_{I_s}(z_s)`:

(i) if every `h_t(y) = d_tᵀ y` is linear and `P_[n] ≤ D_X/2`, then `Err_[n] ≤ 0`;

(ii) if every `h_t : Y → ℝ` is differentiable and `H`-smooth, `H > 0`, and
`c_t = u_t − H⁻¹ ∇h_t(u_t) ∈ Y`, then `Err_[n] ≤ H P_[n]² n / 8`.

**Formalization Note.** In (ii) `h_t` is known on `Y` only, so its gradient is an oracle `gh t`
within `Y`. No convexity of `h_t` is assumed, as printed. -/
theorem theorem_6 {d : ℕ} (hd : 0 < d) (n : ℕ) (hn : 1 ≤ n) (DX : ℝ) (hDX : 0 < DX) (u : ℕ → EuclideanSpace ℝ (Fin d))
    (hu : ∀ t ∈ Finset.Icc 1 n, u t ∈ Metric.closedBall 0 (DX / 2)) :
    (∀ dv : ℕ → EuclideanSpace ℝ (Fin d), pathLengthOn u 1 n ≤ DX / 2 →
      TwoPieceComparators (Metric.closedBall 0 DX) (fun t y => inner ℝ (dv t) y) u n 0) ∧
    (∀ (h : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (gh : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (H : ℝ), 0 < H →
      (∀ t ∈ Finset.Icc 1 n, IsSmoothOn (Metric.closedBall 0 DX) H (h t) (gh t)) →
      (∀ t ∈ Finset.Icc 1 n, u t - H⁻¹ • gh t (u t) ∈ Metric.closedBall 0 DX) →
      TwoPieceComparators (Metric.closedBall 0 DX) h u n
        (H * pathLengthOn u 1 n ^ 2 * n / 8)) := by sorry

end IntervalToDynamic
