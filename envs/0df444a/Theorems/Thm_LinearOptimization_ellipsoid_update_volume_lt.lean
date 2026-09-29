-- Prove2me | Theorems.Thm_LinearOptimization_ellipsoid_update_volume_lt
-- name    : LinearOptimization.ellipsoid_update_volume_lt
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-09T17:05:22.961339+00:00
-- url     : https://prove2.me/theorems/36a397dc-018c-4018-b88e-52405f053393
-- title:
--   Strict volume decrease under the central-cut ellipsoid update
-- statement:
--   Let $n \ge 2$, let $E(z,D)$ be an ellipsoid with $D$ symmetric positive definite, and let $a \in \mathbb R^n$ be nonzero. Let $\bar z$ and $\bar D$ be the central-cut updates
--
--   $$
--   \bar z=z+\frac{1}{n+1}\frac{Da}{\sqrt{a^{\mathsf T}Da}},\qquad
--   \bar D=\frac{n^2}{n^2-1}\left(D-\frac{2}{n+1}\frac{Daa^{\mathsf T}D}{a^{\mathsf T}Da}\right).
--   $$
--
--   The updated ellipsoid has strictly smaller volume:
--
--   $$
--   \operatorname{Vol}(E(\bar z,\bar D))<
--   \exp\!\left(-\frac{1}{2(n+1)}\right)\operatorname{Vol}(E(z,D)).
--   $$
--
--   This is the quantitative volume-shrinkage component of Theorem 8.1 used to bound the number of ellipsoid-method iterations.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 8.1, p. 366, proof in Section 8.2, pp. 366–369

import Definitions.Def_LinearOptimization_EllipsoidMethod

open Matrix MeasureTheory

theorem LinearOptimization.ellipsoid_update_volume_lt {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    volume (ellipsoid (ellipsoidUpdateCenter z D a)
        (ellipsoidUpdateMatrix D a)) <
      ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * ((n : ℝ) + 1)))) *
        volume (ellipsoid z D) := by
  sorry
