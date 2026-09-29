-- Prove2me | Theorems.Thm_LinearOptimization_polyhedron_full_dim_volume_lower_bound_nonstrict
-- name    : LinearOptimization.polyhedron_full_dim_volume_lower_bound_nonstrict
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-10T03:41:03.939086+00:00
-- url     : https://prove2.me/theorems/fb7b6e9a-9aa2-43d3-a5f6-be9215320a39
-- title:
--   Corrected volume lower bound $n^{-n}(nU)^{-n^2(n+1)} \le \mathrm{Vol}(P)$
-- statement:
--   **Corrected boundary-sharp form of Lemma 8.4.** Let $P=\{x\in\mathbb{R}^n:Ax\ge b\}$ be a full-dimensional bounded polyhedron, where $n>0$, the entries of $A$ and $b$ are integers, and their absolute values are bounded by the integer $U$. Then
--
--   $$n^{-n}(nU)^{-n^2(n+1)}\le \operatorname{Vol}(P).$$
--
--   This keeps the constant and every hypothesis of the printed lemma, but replaces its false strict inequality by a non-strict inequality. The correction is sharp: for $n=U=1$ and $P=[0,1]$, both sides equal $1$.
-- source:
--   Corrected boundary-sharp form of Bertsimas and Tsitsiklis, Introduction to Linear Optimization (Athena Scientific, 1997), Lemma 8.4, p. 376 and its proof on pp. 376-377. The printed strict inequality is false at n = U = 1, P = [0,1]; the corrected statement replaces > by ≥ and leaves the hypotheses and constant unchanged.

import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_Polyhedron

open Matrix MeasureTheory

theorem LinearOptimization.polyhedron_full_dim_volume_lower_bound_nonstrict
    {m n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (U : ℤ)
    (hA : ∀ i j, |A i j| ≤ U) (hb : ∀ i, |b i| ≤ U)
    (hbdd : LinearOptimization.IsBoundedSet
      (LinearOptimization.polyhedron
        (A.map ((↑) : ℤ → ℝ)) (fun i => (b i : ℝ))))
    (hfull : LinearOptimization.IsFullDimensional
      (LinearOptimization.polyhedron
        (A.map ((↑) : ℤ → ℝ)) (fun i => (b i : ℝ)))) :
    ENNReal.ofReal
        (((n : ℝ) ^ n * ((n : ℝ) * (U : ℝ)) ^ (n ^ 2 * (n + 1)))⁻¹) ≤
      volume (LinearOptimization.polyhedron
        (A.map ((↑) : ℤ → ℝ)) (fun i => (b i : ℝ))) := by
  sorry
