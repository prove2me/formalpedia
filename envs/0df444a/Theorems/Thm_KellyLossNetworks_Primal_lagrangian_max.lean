-- Prove2me | Theorems.Thm_KellyLossNetworks_Primal_lagrangian_max
-- name    : KellyLossNetworks.Primal.lagrangian_max
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:06:49.291631+00:00
-- url     : https://prove2.me/theorems/b20e7e06-84d7-4095-82b3-6f2cdc94a691
-- title:
--   Equation (2.2): the Lagrangian maximum and dual value
-- statement:
--   For offered traffic $\nu_r>0$ and any nonnegative multiplier vector $y$, let $L(x,z;y)$ be the Lagrangian of the primal problem with nonnegative route flow $x$ and slack $z$. Its maximum is attained at $x_r=\nu_r e^{-\sum_jy_jA_{jr}}$ and $z=0$, with value
--
--   $$\max_{x,z\ge0}L(x,z;y)=\sum_r\nu_r e^{-\sum_jy_jA_{jr}}+\sum_jy_jC_j.$$
--
--   This identifies the published dual objective as the Lagrangian maximum.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, pp. 327–328, §2.1, (2.2) and the display following it

import Mathlib
import Definitions.Def_KellyLossNetworks_Primal_Problem

namespace KellyLossNetworks.Primal

/-- Kelly, *Loss networks* (1991), §2.1, pp. 327–328, Lagrangian and (2.2)–(2.3).
Formalization Note: `z = 0` is a maximizing slack vector when `y ≥ 0`. -/
theorem lagrangian_max {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r)
    (y : Fin J → ℝ) (hy : ∀ j, 0 ≤ y j) :
    (∀ (x : Fin R → ℝ) (z : Fin J → ℝ),
      (∀ r, 0 ≤ x r) → (∀ j, 0 ≤ z j) →
      lagrangian A ν C x z y ≤ KellyStochasticNetworks.dualObjective A ν C y) ∧
    lagrangian A ν C (primalPoint A ν y) (fun _ => 0) y =
      KellyStochasticNetworks.dualObjective A ν C y := by sorry

end KellyLossNetworks.Primal
