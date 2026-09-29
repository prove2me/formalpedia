-- Prove2me | Theorems.Thm_NoetherIVP_invariance_pointwise
-- name    : NoetherIVP.invariance_pointwise
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T14:57:03.379146+00:00
-- url     : https://prove2.me/theorems/3ab135d3-4756-4495-92cb-fd5d4f5c4108
-- title:
--   Noether (1918), eqs. (10)–(11): from $\Delta I = 0$ to $\delta f + \operatorname{Div}(f\,\Delta x) = 0$
-- statement:
--   **Equations (10)–(11) of the paper.** Noether's invariance hypothesis is that
--   $$\int \bigl( \delta f + \operatorname{Div}(f[u]\,\Delta x) \bigr)\,dx \;=\; 0$$
--   over *every* region; she then concludes, "since the relation is satisfied for integration over
--   any arbitrary interval, the integrand must vanish identically", that
--   $$\delta f(x) + \operatorname{Div}\bigl(f[u]\,\Delta x\bigr)(x) \;=\; 0 \qquad \text{for all } x,$$
--   which is Lie's differential equation for the invariance of $I$.
--
--   Formally: if the function
--   $y \mapsto \delta f(y) + \operatorname{Div}\bigl(f[u]\,\Delta x\bigr)(y)$ is continuous and its
--   integral over every closed ball of $\mathbb{R}^n$ vanishes, then it vanishes at every point.
-- source:
--   E. Noether, Invariante Variationsprobleme (1918), Tavel translation, arXiv:physics/0503066v3, §2, p. 5, equations (10) and (11).

import Mathlib
import Definitions.Def_NoetherIVP_core

namespace NoetherIVP
theorem invariance_pointwise {n m : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → Fin m → ℝ) → ℝ)
    (u du : (Fin n → ℝ) → Fin m → ℝ) (dx : (Fin n → ℝ) → Fin n → ℝ)
    (hcont : Continuous fun y => varF f u du y + divg (fun z l => lagr f u z * dx z l) y)
    (hI : ∀ (c : Fin n → ℝ) (r : ℝ),
      (∫ y in Metric.closedBall c r,
        (varF f u du y + divg (fun z l => lagr f u z * dx z l) y)) = 0) :
    ∀ x : Fin n → ℝ,
      varF f u du x + divg (fun z l => lagr f u z * dx z l) x = 0 := by sorry
end NoetherIVP
