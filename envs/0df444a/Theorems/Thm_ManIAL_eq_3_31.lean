-- Prove2me | Theorems.Thm_ManIAL_eq_3_31
-- name    : ManIAL.eq_3_31
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:12:58.640984+00:00
-- url     : https://prove2.me/theorems/2f5af21d-c8be-4b38-b9b2-1c980105c4d8
-- title:
--   Display (3.31) — the dual iterates are bounded by $z_{\max}$
-- statement:
--   Let $\mathcal A$ be linear, $\beta_0>0$, and let $x^k\in\mathbb R^n$, $y^k\in\mathbb R^m$ be arbitrary sequences. Define $z^0=0$ and $z^{k+1}=z^k-\beta_{k+1}(\mathcal Ax^{k+1}-y^{k+1})$ with the dual step size (3.13),
--   $\beta_{k+1}=\beta_0\min\big(\|\mathcal Ax^0-y^0\|\log^22/(\|\mathcal Ax^{k+1}-y^{k+1}\|(k+1)^2\log(k+2)),1\big)$. Then for every $k\ge0$
--
--   $$
--   \|z^k\|\le z_{\max}:=\frac{\beta_0\pi^2}6\|\mathcal Ax^0-y^0\| .
--   $$
--
--   The bound holds whatever the primal iterates are, which is why ManIAL's multipliers stay bounded while the penalty $\sigma_k$ grows; it feeds the feasibility bound (3.32) and the constants of Theorems 3.5, 3.6 and 3.8.
--
--   Differences from the source:
--   - generalization: ‖z^{k+1}‖ ≤ z_max for any k > 1, for the iterates of Algorithm 1 → ‖z^k‖ ≤ z_max for every k ≥ 0, for any sequences x^k, y^k; reason: contains the printed range; the argument uses only (3.13), (3.14) and z⁰ = 0
--   - generalization: y⁰ = Ax⁰ (Algorithm 1, step 2) → y⁰ arbitrary; reason: the bound (3.31) only uses (3.13); y⁰ = Ax⁰ is the special case (then z^k ≡ 0)
--   - reading: dual step size β₀ → β₀ > 0; reason: a step size; (3.31) needs β₀ ≥ 0
--   - encoding: log in (3.13); division by ‖Ax^{k+1} − y^{k+1}‖ = 0 → Real.log; Lean's x/0 = 0 gives β_{k+1} = 0; reason: β_{k+1} only enters through β_{k+1}(Ax^{k+1} − y^{k+1}) = 0, so the iterates are the same; (3.31) holds for the natural log
-- source:
--   Deng, Hu, Wu & Wen, Oracle complexities of augmented Lagrangian methods for nonsmooth manifold optimization, arXiv:2404.05121v2, display (3.31), p.12

import Mathlib
import Definitions.Def_ManIAL_dualStep

namespace ManIAL

/-- **Display (3.31)** (Deng–Hu–Wu–Wen, arXiv:2404.05121v2, p.12): the dual iterates of
Algorithm 1 are uniformly bounded. If `z⁰ = 0` and `z^{k+1} = z^k − β_{k+1}(Ax^{k+1} − y^{k+1})`
with `β_{k+1}` from (3.13) and `β₀ > 0`, then for every `k`,
`‖z^k‖ ≤ z_max := (β₀π²/6)‖Ax⁰ − y⁰‖`, whatever the sequences `x^k`, `y^k`.

**Formalization Note.** The printed display is for `z^{k+1}`, "for any `k > 1`"; it is stated
here for every `k`. `log` in (3.13) is the natural logarithm. -/
theorem eq_3_31 {n m : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (β₀ : ℝ) (hβ₀ : 0 < β₀) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (y z : ℕ → EuclideanSpace ℝ (Fin m)) (hz0 : z 0 = 0)
    (hz : ∀ k : ℕ, z (k + 1) =
      z k - dualStep β₀ A (x 0) (y 0) k (x (k + 1)) (y (k + 1)) • (A (x (k + 1)) - y (k + 1))) :
    ∀ k : ℕ, ‖z k‖ ≤ β₀ * Real.pi ^ 2 / 6 * ‖A (x 0) - y 0‖ := by sorry

end ManIAL
