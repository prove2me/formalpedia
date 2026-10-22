-- Prove2me | Theorems.Thm_GeomDL_RNN_shift_equivariant_s_steps
-- name    : GeomDL.RNN.shift_equivariant_s_steps
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:37.770041+00:00
-- url     : https://prove2.me/theorems/22320a55-481a-420e-a152-a0e43f17c6bf
-- title:
--   §5.7, side-note p. 93 — equivariance under an s-step left shift
-- statement:
--   Let $R:\mathbb R^k\times\mathbb R^m\to\mathbb R^m$ be any RNN update map, $h_0\in\mathbb R^m$ its seed, and $\bar z$ an input sequence padded on the left by $d$ zero vectors. If $0\le s\le d$ and $R(0,h_0)=h_0$, then the RNN run on the sequence shifted left by $s$ steps is the correspondingly shifted original run:
--
--   $$
--   h_{\bar z(\cdot+s)}(t)=h_{\bar z}(t+s)\qquad\text{for every }t\ge0.
--   $$
--
--   This extends the one-step statement to all shifts that fit inside the zero padding.
--
--   **Formalization Note** Time is indexed by natural numbers, and the original input begins at time $1$; its value at time $0$ is unused.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §5.7, side-note, p. 93

import Mathlib
import Definitions.Def_GeomDL_RNN_Recurrence

namespace GeomDL.RNN

/-- The side-note on p. 93: padding by at least `s` permits an `s`-step left shift. -/
theorem shift_equivariant_s_steps {k m : ℕ}
    (R : (Fin k → ℝ) → (Fin m → ℝ) → (Fin m → ℝ))
    (h0 : Fin m → ℝ) (z : ℕ → Fin k → ℝ)
    (delay s : ℕ) (hpad : s ≤ delay) (hfix : R 0 h0 = h0) :
    ∀ t : ℕ,
      run R h0 (fun u => pad delay z (u + s)) t =
        run R h0 (pad delay z) (t + s) := by sorry

end GeomDL.RNN
