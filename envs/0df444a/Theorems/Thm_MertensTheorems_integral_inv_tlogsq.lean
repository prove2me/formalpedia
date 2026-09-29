-- Prove2me | Theorems.Thm_MertensTheorems_integral_inv_tlogsq
-- name    : MertensTheorems.integral_inv_tlogsq
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:57:49.967418+00:00
-- url     : https://prove2.me/theorems/919a7a12-5623-40a0-ac01-bec768221c03
-- title:
--   The integral of $1/(t\log^2 t)$ in closed form
-- statement:
--   **A convergent companion to the $\log\log$ integral.**
--
--   For $N \ge 2$,
--
--   $$\int_{2}^{N}\frac{dt}{t\log^{2} t} \;=\; \frac{1}{\log 2} - \frac{1}{\log N}.$$
--
--   The integrand is the derivative of $-1/\log t$: indeed
--   $\tfrac{d}{dt}\bigl(-\tfrac{1}{\log t}\bigr) = \tfrac{1}{\log^{2}t}\cdot\tfrac1t$. On $[2,N]$
--   the integrand is continuous since $\log t \ge \log 2 > 0$, so the fundamental theorem of
--   calculus applies.
--
--   The contrast with $\int \tfrac{dt}{t\log t} = \log\log N - \log\log 2$ is the point: raising the
--   logarithm to the second power turns a **divergent** integral into a **convergent** one, the
--   limit as $N \to \infty$ being $1/\log 2$. This is the precise sense in which $\sum_p 1/p$
--   diverges while $\sum_p \tfrac{1}{p\log p}$ converges, and it is the estimate used to bound the
--   tail contributions that Mertens-type partial summation leaves behind.
--
--   **Formalization note.** The integral is `intervalIntegral` over $[2,N]$ with $N$ cast from
--   $\mathbb{N}$; $N \ge 2$ keeps the interval non-degenerate.
-- source:
--   Classical; see Apostol, *Introduction to Analytic Number Theory*, §4.3. Lean proof extracted from `Salt/Maynard/Mertens.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace MertensTheorems

theorem integral_inv_tlogsq {N : ℕ} (hN : 2 ≤ N) :
    ∫ t in (2 : ℝ)..N, (t * Real.log t ^ 2)⁻¹
      = (Real.log 2)⁻¹ - (Real.log N)⁻¹ := by sorry

end MertensTheorems
