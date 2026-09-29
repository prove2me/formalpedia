-- Prove2me | Theorems.Thm_MertensTheorems_continuousOn_inv_tlogsq
-- name    : MertensTheorems.continuousOn_inv_tlogsq
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T18:06:48.741656+00:00
-- url     : https://prove2.me/theorems/baa76a97-8277-4b65-ae07-6dca8d25987d
-- title:
--   Continuity of $1/(t\log^2 t)$ on $[2,N]$
-- statement:
--   **The integrand $1/(t\log^{2}t)$ is continuous on $[2,N]$.**
--
--   For $N \ge 2$, the function $t \mapsto (t\log^{2}t)^{-1}$ is continuous on the interval
--   $[2,N]$.
--
--   The only obstruction to continuity of a reciprocal is a zero of the denominator, and on
--   $[2,N]$ there is none: $t \ge 2 > 0$ and $\log t \ge \log 2 > 0$, so $t\log^{2}t \ge 2\log^{2}2 > 0$
--   throughout. Away from $t = 1$ and $t = 0$, where $\log$ vanishes or is undefined, the function
--   is a composition of continuous maps.
--
--   Continuity on a compact interval is exactly the hypothesis that the fundamental theorem of
--   calculus requires, so this is the lemma that licenses evaluating
--   $\int_{2}^{N} \tfrac{dt}{t\log^{2}t} = \tfrac{1}{\log 2} - \tfrac{1}{\log N}$. Statements of
--   this kind are the unglamorous side conditions that every integral evaluation in analytic number
--   theory carries, and they are worth isolating because the interval endpoints recur.
--
--   **Formalization note.** `Set.uIcc 2 N` is the unordered closed interval, which equals $[2,N]$
--   under the hypothesis $N \ge 2$ but is well defined regardless of the order of the endpoints.
-- source:
--   Standard. Lean proof extracted from `Salt/Maynard/Mertens.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace MertensTheorems

theorem continuousOn_inv_tlogsq {N : ℕ} (hN : 2 ≤ N) :
    ContinuousOn (fun t : ℝ => (t * Real.log t ^ 2)⁻¹) (Set.uIcc 2 (N : ℝ)) := by sorry

end MertensTheorems
