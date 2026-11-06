-- Prove2me | Theorems.Thm_MatrixLeeSidford_lemma_5_4
-- name    : MatrixLeeSidford.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:30:50.060755+00:00
-- url     : https://prove2.me/theorems/c6876a3a-1e68-4050-a670-774989bdd261
-- title:
--   Lemma 5.4 — first-order approximation of a minimizer
-- statement:
--   Let $U$ be an open subset of a Euclidean space $\mathbb R^d$ and $f(t,z)$ a smooth function of $t\in\mathbb R$ and $z\in U$. Suppose that for every $t$ near $0$ the point $z_*(t)\in U$ minimizes $f(t,\cdot)$ over $U$, that $z_*$ is smooth, and that $H=\nabla_z^2f(0,z_*(0))$ is positive definite. Let $z(t)$ be a smooth curve with $z(0)=z_*(0)$.
--   1. If $z'(0)=z_*'(0)$, then $f(t,z(t))-f(t,z_*(t))=O(t^4)$ as $t\to0$.
--   2. The second derivatives at $t=0$ satisfy
--   $$
--   \frac{d^2}{dt^2}f(t,z(t))\Big|_{t=0}\ \ge\ \frac{d^2}{dt^2}f(t,z_*(t))\Big|_{t=0},
--   $$
--   with equality if and only if $z'(0)=z_*'(0)$.
--
--   The lemma lets derivatives of an optimal value up to third order be computed from the optimal weight to first order.
--
--   **Formalization Note** $f$ is $C^\infty$ on $\mathbb R\times U$; the curves $z,z_*$ are $C^\infty$ maps $\mathbb R\to\mathbb R^d$; $H$ is the second Fréchet derivative of $f(0,\cdot)$ at $z_*(0)$.
--
--   Differences from the source:
--   - encoding: f smooth on ℝ × (open subset of a Euclidean space); z, z_* smooth curves; 'for every t near 0'; O(t⁴) → ContDiffOn ℝ ∞ f (univ ×ˢ U) with U ⊆ EuclideanSpace ℝ (Fin d) open; z, z_* : ℝ → EuclideanSpace with ContDiff ℝ ∞; ∀ᶠ t in 𝓝 0; Asymptotics.IsBigO at 𝓝 0; reason: every conclusion is local at t = 0, and a curve smooth near 0 agrees near 0 with a globally smooth one (bump function), so no instance is lost
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Lemma 5.4, p.41

import Mathlib

open Matrix Filter Topology
open scoped ContDiff Pointwise

namespace MatrixLeeSidford

/-- **Lemma 5.4 (First-order approximation of a minimizer)** (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), pp.41–42). Let `f(t, z)` be
smooth in `t ∈ ℝ` and `z` in an open subset `U` of a Euclidean space. Suppose that for every `t`
near `0` the point `z_*(t)` minimizes `f(t, ·)`, that `z_*` is smooth, and that
`H := ∇²_z f(0, z_*(0))` is positive definite. Let `z(t)` be a smooth curve with `z(0) = z_*(0)`.
(a) If `z'(0) = z_*'(0)`, then `f(t, z(t)) − f(t, z_*(t)) = O(t⁴)`. (b) `d²/dt² f(t, z(t))|₀ ≥
d²/dt² f(t, z_*(t))|₀`, with equality if and only if `z'(0) = z_*'(0)`.

**Formalization Note** The Euclidean space is `EuclideanSpace ℝ (Fin d)`; "smooth" is `C^∞`
(`f` on `ℝ × U`, the curves on `ℝ`); "for every `t` near 0" is an eventually-in-`𝓝 0` statement;
minimization is over `U`; `O(t⁴)` is `Asymptotics.IsBigO` at `t → 0`; the Hessian is
`iteratedFDeriv ℝ 2`. -/
theorem lemma_5_4 {d : ℕ} (U : Set (EuclideanSpace ℝ (Fin d))) (hU : IsOpen U)
    (f : ℝ × EuclideanSpace ℝ (Fin d) → ℝ) (hf : ContDiffOn ℝ ∞ f (Set.univ ×ˢ U))
    (zstar z : ℝ → EuclideanSpace ℝ (Fin d)) (hzstar : ContDiff ℝ ∞ zstar)
    (hz : ContDiff ℝ ∞ z)
    (hmin : ∀ᶠ t in 𝓝 (0 : ℝ), zstar t ∈ U ∧ ∀ w ∈ U, f (t, zstar t) ≤ f (t, w))
    (hH : ∀ w : EuclideanSpace ℝ (Fin d), w ≠ 0 →
      0 < iteratedFDeriv ℝ 2 (fun x => f (0, x)) (zstar 0) (fun _ => w))
    (hz0 : z 0 = zstar 0) :
    (deriv z 0 = deriv zstar 0 →
      (fun t : ℝ => f (t, z t) - f (t, zstar t)) =O[𝓝 0] (fun t : ℝ => t ^ 4)) ∧
    iteratedDeriv 2 (fun t : ℝ => f (t, zstar t)) 0 ≤ iteratedDeriv 2 (fun t : ℝ => f (t, z t)) 0 ∧
    (iteratedDeriv 2 (fun t : ℝ => f (t, z t)) 0 = iteratedDeriv 2 (fun t : ℝ => f (t, zstar t)) 0 ↔
      deriv z 0 = deriv zstar 0) := by sorry

end MatrixLeeSidford
