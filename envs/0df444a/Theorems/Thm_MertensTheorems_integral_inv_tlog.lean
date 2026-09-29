-- Prove2me | Theorems.Thm_MertensTheorems_integral_inv_tlog
-- name    : MertensTheorems.integral_inv_tlog
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:47:16.74235+00:00
-- url     : https://prove2.me/theorems/d79eee94-11fe-4705-8930-1cd224c8fde8
-- title:
--   The integral of $1/(t\log t)$ is a difference of iterated logarithms
-- statement:
--   **The closed form of the $\log\log$ integral.**
--
--   For $N \ge 2$,
--
--   $$\int_{2}^{N} \frac{dt}{t\log t} \;=\; \log\log N \;-\; \log\log 2 .$$
--
--   The integrand is the derivative of $\log\log t$: by the chain rule,
--   $\tfrac{d}{dt}\log\log t = \tfrac{1}{\log t}\cdot\tfrac1t$. On $[2,N]$ the function $\log t$ is
--   bounded away from $0$ (indeed $\log t \ge \log 2 > 0$), so the integrand is continuous and the
--   fundamental theorem of calculus applies directly.
--
--   This integral is the reason $\log\log$ appears throughout multiplicative number theory. Partial
--   summation converts Mertens' first theorem $\sum_{p\le N}\tfrac{\log p}{p} = \log N + O(1)$ into
--   $\sum_{p\le N}\tfrac1p$ by integrating $\tfrac{1}{t\log t}$ against the error term, and the
--   closed form above is exactly what produces the main term $\log\log N$ in Mertens' second
--   theorem. The same integral governs the divergence of $\sum_p 1/p$ and the typical number of
--   prime factors of an integer, $\omega(n) \approx \log\log n$, in the Hardy–Ramanujan and
--   Erd\H{o}s–Kac theorems.
--
--   **Formalization note.** The integral is `intervalIntegral` over $[2, N]$ with $N$ cast from
--   $\mathbb{N}$; the hypothesis $N \ge 2$ keeps the interval non-degenerate and the integrand
--   regular.
-- source:
--   Classical; the analytic step from Mertens' first to his second theorem, see Apostol, *Introduction to Analytic Number Theory*, §4.3. Lean proof extracted from `Salt/Maynard/Mertens.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace MertensTheorems

theorem integral_inv_tlog {N : ℕ} (hN : 2 ≤ N) :
    ∫ t in (2 : ℝ)..N, (t * Real.log t)⁻¹
      = Real.log (Real.log N) - Real.log (Real.log 2) := by sorry

end MertensTheorems
