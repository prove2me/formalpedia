-- Prove2me | Theorems.Thm_LinearOptimization_ellipsoid_update_halfspace_subset
-- name    : LinearOptimization.ellipsoid_update_halfspace_subset
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-09T17:05:08.184688+00:00
-- url     : https://prove2.me/theorems/9d1ebf90-62c4-4267-bf4c-ab6288c9adba
-- title:
--   The central half-ellipsoid is contained in the updated ellipsoid
-- statement:
--   Let $n \ge 2$, let $E(z,D)$ be an ellipsoid with $D$ symmetric positive definite, and let $a \in \mathbb R^n$ be nonzero. Put
--
--   $$
--   H=\{x\in\mathbb R^n\mid a^{\mathsf T}x\ge a^{\mathsf T}z\},\qquad
--   \bar z=z+\frac{1}{n+1}\frac{Da}{\sqrt{a^{\mathsf T}Da}},
--   $$
--
--   and
--
--   $$
--   \bar D=\frac{n^2}{n^2-1}\left(D-\frac{2}{n+1}\frac{Daa^{\mathsf T}D}{a^{\mathsf T}Da}\right).
--   $$
--
--   Then
--
--   $$
--   E(z,D)\cap H\subseteq E(\bar z,\bar D).
--   $$
--
--   This is the geometric covering component of the central-cut ellipsoid update in Theorem 8.1.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 8.1, p. 366, proof in Section 8.2, pp. 366–369

import Definitions.Def_LinearOptimization_EllipsoidMethod

open Matrix

theorem LinearOptimization.ellipsoid_update_halfspace_subset {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    ellipsoid z D ∩ {x | a ⬝ᵥ z ≤ a ⬝ᵥ x} ⊆
      ellipsoid (ellipsoidUpdateCenter z D a) (ellipsoidUpdateMatrix D a) := by
  sorry
