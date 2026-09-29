-- Prove2me | Theorems.Thm_Mandelbrot_multibrot_escape_criterion
-- name    : Mandelbrot.multibrot_escape_criterion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T01:59:07.337811+00:00
-- url     : https://prove2.me/theorems/2108037c-5fba-4513-84d7-7aaf11960d47
-- title:
--   Escape criterion for Multibrot sets, $2 \le n$
-- statement:
--   **Escape criterion for Multibrot sets.** Let $n \ge 2$ and $f_{n,c}(z) = z^{n} + c$. Then $c$ lies in the Multibrot set $M_n$ if and only if
--
--   $$\left| f_{n,c}^{\,k}(0) \right| \le 2^{1/(n-1)} \qquad \text{for every } k \in \mathbb{N}.$$
--
--   The radius $r_n = 2^{1/(n-1)}$ is the standard escape radius for the degree-$n$ unicritical family: it is the positive solution of $r^{n} = 2r$, the threshold past which the estimate $|z^{n} + c| \ge |z|^{n} - |c|$ forces the orbit to grow. For $n = 2$ it specialises to the familiar radius $2$.
-- source:
--   https://en.wikipedia.org/wiki/Multibrot_set

import Definitions.Def_mandelbrot_sets
open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

/-- For `2 ≤ n`, the Multibrot set of power `n` is exactly the set of parameters `c` whose
critical orbit stays in the closed disk of radius `2 ^ (n - 1)⁻¹`. -/
theorem multibrot_escape_criterion {n : ℕ} (hn : 2 ≤ n) :
    multibrotSet n =
      {c : ℂ | ∀ k : ℕ, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ (2 : ℝ) ^ (((n : ℝ) - 1)⁻¹)} := by
  sorry

end Mandelbrot
