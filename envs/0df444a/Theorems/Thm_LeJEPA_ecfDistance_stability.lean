-- Prove2me | Theorems.Thm_LeJEPA_ecfDistance_stability
-- name    : LeJEPA.ecfDistance_stability
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T11:26:22.223389+00:00
-- url     : https://prove2.me/theorems/ec12b049-6b3f-4608-8690-3934cd71cf2c
-- title:
--   Theorem 4 (as proved): bounded gradient and curvature of the empirical characteristic-function distance
-- statement:
--   Let $N\ge1$, $s>0$, $z\in\mathbb{R}^N$ and $i\le N$. Write $\hat D_V(z)=\int e^{-s^2t^2}|\hat\varphi_N(t)-e^{-t^2/2}|^2\,dt$ with $\hat\varphi_N(t)=\frac1N\sum_je^{itz_j}$, viewed as a function of the single sample $z_i$. Then $\hat D_V$ is differentiable in $z_i$ with
--
--   $$\Big|\frac{\partial\hat D_V}{\partial z_i}\Big|\le\frac{4}{Ns^2},$$
--
--   and there is an absolute constant $C$ such that $\hat D_V$ is twice continuously differentiable in $z_i$ with
--
--   $$\Big|\frac{\partial^2\hat D_V}{\partial z_i^2}\Big|\le\frac{C}{N}\cdot\frac{\sqrt\pi}{2s^3}.$$
--
--   With $s=1/\sigma$ the first bound is $4\sigma^2/N$.
--
--   **Formalization Note** This is the statement the proof in Appendix B.12 establishes, for the statistic $\hat D_V$ without the factor $N$. Theorem 4 in Section 4.2.3 states the same bounds for the Epps–Pulley statistic $EP=N\hat D_V$; for $EP$ the first derivative is bounded by $4\sigma^2$, not $4\sigma^2/N$. With all $N$ samples equal, the derivative of $EP$ does not depend on $N$.
-- source:
--   Balestriero and LeCun, LeJEPA: Provable and Scalable Self-Supervised Learning Without the Heuristics, arXiv:2511.08544v3 (2025), Section 4.2.3, Theorem 4, in the form established by its proof in Appendix B.12 (weight $w_s(t)=e^{-s^2t^2}$, $\sigma = 1/s$)

import Mathlib
import Definitions.Def_LeJEPA_Basic

open MeasureTheory Matrix Filter Topology
open scoped ENNReal InnerProductSpace

namespace LeJEPA

theorem ecfDistance_stability :
    (∀ (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 0 < s) (z : Fin N → ℝ) (i : Fin N),
      DifferentiableAt ℝ (fun y => ecfDistance s (Function.update z i y)) (z i) ∧
      |deriv (fun y => ecfDistance s (Function.update z i y)) (z i)| ≤ 4 / (N * s ^ 2)) ∧
    ∃ C : ℝ, ∀ (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 0 < s) (z : Fin N → ℝ) (i : Fin N),
      ContDiff ℝ 2 (fun y => ecfDistance s (Function.update z i y)) ∧
      |deriv (deriv (fun y => ecfDistance s (Function.update z i y))) (z i)| ≤ C / N * (Real.sqrt Real.pi / (2 * s ^ 3)) := by sorry

end LeJEPA
