-- Prove2me | Theorems.Thm_GroverWiki_iterationCount_le
-- name    : GroverWiki.iterationCount_le
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T14:35:37.106629+00:00
-- url     : https://prove2.me/theorems/58e602ff-405c-407d-b5e4-8bc71e253506
-- title:
--   Iteration count: $r(N) = \lfloor \pi/(4\arcsin(1/\sqrt N))\rfloor \le \lceil \frac{\pi}{4}\sqrt N\rceil$
-- statement:
--   Let $N \ge 1$ and $t = \arcsin(1/\sqrt N)$. The number of Grover iterations $r(N) = \lfloor \pi/(4t)\rfloor$ satisfies
--
--   $$r(N) = \left\lfloor \frac{\pi}{4\arcsin(1/\sqrt N)} \right\rfloor \le \left\lceil \frac{\pi}{4}\sqrt N \right\rceil .$$
--
--   Together with the error bound for this choice of $r$ (milestone *Algebraic proof — stopping at $r = \lfloor\pi/(4t)\rfloor$*), this is the source's statement that the correctly chosen number of iterations is at most $\lceil\frac{\pi}{4}\sqrt N\rceil$, i.e. $O(\sqrt N)$ applications of the oracle.
--
--   **Formalization Note** The source does not fix a rounding convention for "$r = \pi/4t$"; the mission uses the integer part $\lfloor\pi/(4t)\rfloor$.
-- source:
--   Wikipedia, "Grover's algorithm", revision oldid=1373498442, https://en.wikipedia.org/w/index.php?title=Grover%27s_algorithm&oldid=1373498442, section "Algorithm" (PDF p. 4), with $r = \pi/4t$ from section "Algebraic proof" (PDF p. 6)

import Mathlib
import Definitions.Def_GroverWiki_Defs

open Matrix

namespace GroverWiki

/-- The number of iterations `r(N) = ⌊π/(4 arcsin(1/√N))⌋` satisfies `r(N) ≤ ⌈(π/4)√N⌉`. -/
theorem iterationCount_le {N : ℕ} (hN : 1 ≤ N) :
    ⌊Real.pi / (4 * Real.arcsin (1 / Real.sqrt N))⌋₊ ≤ ⌈Real.pi / 4 * Real.sqrt N⌉₊ := by sorry

end GroverWiki
