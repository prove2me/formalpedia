-- Prove2me | Theorems.Thm_GroverWiki_grover_search
-- name    : GroverWiki.grover_search
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T14:42:41.667632+00:00
-- url     : https://prove2.me/theorems/994670b7-83b1-4d17-a182-da6b2b63ab40
-- title:
--   Grover's algorithm finds the marked item with probability $\ge 1 - 1/N$ within $\lceil\frac{\pi}{4}\sqrt N\rceil$ iterations
-- statement:
--   Let $N \ge 1$ and let $f\colon\{0,1,\dots,N-1\}\to\{0,1\}$ have exactly one index $\omega$ with $f(\omega) = 1$. Let $U_\omega|x\rangle = (-1)^{f(x)}|x\rangle$ be the oracle, $|s\rangle = \frac{1}{\sqrt N}\sum_x |x\rangle$ the uniform superposition and $U_s = 2|s\rangle\langle s| - I$ the Grover diffusion operator. Then there is a number of iterations $r$ with
--
--   $$r \le \left\lceil \frac{\pi}{4}\sqrt N\right\rceil \qquad\text{and}\qquad \bigl|\langle\omega|(U_sU_\omega)^r|s\rangle\bigr|^2 \ge 1 - \frac1N .$$
--
--   That is, Grover's algorithm — prepare $|s\rangle$, apply the Grover iteration $U_sU_\omega$ $r$ times, measure in the computational basis — outputs $\omega$ with probability at least $1 - 1/N$ (in particular at least $1/2$ for $N \ge 2$, and approaching $1$ for $N \gg 1$) using $r = O(\sqrt N)$ applications of $U_\omega$, compared with the $\Theta(N)$ evaluations needed classically.
-- source:
--   Wikipedia, "Grover's algorithm", revision oldid=1373498442, https://en.wikipedia.org/w/index.php?title=Grover%27s_algorithm&oldid=1373498442, lead section (PDF p. 1), section "Problem description" (PDF pp. 2–3) and section "Algorithm" (PDF p. 4)

import Mathlib
import Definitions.Def_GroverWiki_Defs

open Matrix

namespace GroverWiki

/-- Grover's algorithm: with at most `⌈(π/4)√N⌉` Grover iterations (hence `O(√N)` applications of
`U_ω`), measuring the state yields the unique marked index `ω` with probability at least
`1 - 1/N`. -/
theorem grover_search {N : ℕ} (f : Fin N → Fin 2) (ω : Fin N)
    (hω : ∀ x, f x = 1 ↔ x = ω) :
    ∃ r : ℕ, r ≤ ⌈Real.pi / 4 * Real.sqrt N⌉₊ ∧
      1 - 1 / (N : ℝ) ≤ measureProb (groverState f r) ω := by sorry

end GroverWiki
