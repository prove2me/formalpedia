-- Prove2me | Theorems.Thm_GeomDL_RNN_shift_equivariant_of_fixed_point
-- name    : GeomDL.RNN.shift_equivariant_of_fixed_point
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:35.021059+00:00
-- url     : https://prove2.me/theorems/563a2a76-61e8-4e94-a92d-5ceaf4c3d428
-- title:
--   §5.7, p. 93 — a fixed-point seed makes a padded RNN shift-equivariant
-- statement:
--   Let $R:\mathbb R^k\times\mathbb R^m\to\mathbb R^m$ be an RNN update map, and pad an input sequence $z$ on the left with $d\ge1$ zero vectors to obtain $\bar z$. If the common seed $h_0$ of both runs is a fixed point of the zero-input update, $R(0,h_0)=h_0$, then
--
--   $$
--   h_{\bar z(\cdot+1)}(t)=h_{\bar z}(t+1)\qquad\text{for every }t\ge0.
--   $$
--
--   This is the boundary condition under which an RNN commutes with a one-step left shift of a padded input.
--
--   **Formalization Note** The claim includes $t=0$. The book's $z(1)$ is Lean's input at index $1$, with $z(0)$ unused.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §5.7, paragraph following equations (40)–(41), p. 93

import Mathlib
import Definitions.Def_GeomDL_RNN_Recurrence

namespace GeomDL.RNN

/-- The one-step left-shift equivariance on p. 93. -/
theorem shift_equivariant_of_fixed_point {k m : ℕ}
    (R : (Fin k → ℝ) → (Fin m → ℝ) → (Fin m → ℝ))
    (h0 : Fin m → ℝ) (z : ℕ → Fin k → ℝ)
    (delay : ℕ) (hpad : 1 ≤ delay) (hfix : R 0 h0 = h0) :
    ∀ t : ℕ,
      run R h0 (fun u => pad delay z (u + 1)) t =
        run R h0 (pad delay z) (t + 1) := by sorry

end GeomDL.RNN
