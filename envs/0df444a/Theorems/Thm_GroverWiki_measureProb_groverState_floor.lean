-- Prove2me | Theorems.Thm_GroverWiki_measureProb_groverState_floor
-- name    : GroverWiki.measureProb_groverState_floor
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T14:42:17.300785+00:00
-- url     : https://prove2.me/theorems/997c183b-b814-4e2d-9ca3-4fe4c9b8261d
-- title:
--   Stopping at $r = \lfloor\pi/(4t)\rfloor$, $\omega$ is observed with error at most $1/N$
-- statement:
--   Let $f\colon\{0,\dots,N-1\}\to\{0,1\}$ have exactly one index $\omega$ with $f(\omega) = 1$, let $t = \arcsin(1/\sqrt N)$ and $r = \lfloor \pi/(4t)\rfloor$. After $r$ Grover iterations, measuring the state yields $\omega$ with probability
--
--   $$\bigl|\langle\omega|(U_sU_\omega)^r|s\rangle\bigr|^2 \ge 1 - \frac1N ,$$
--
--   i.e. with error at most $1/N$. This is a quantitative form of the source's claim that stopping at $r = \pi/4t \approx \pi\sqrt N/4$ gives the correct answer with error $O(1/N)$.
--
--   **Formalization Note** The source's $r = \pi/4t$ is in general not an integer; the mission rounds it down, and replaces "$O(1/N)$" by the explicit bound $1/N$.
-- source:
--   Wikipedia, "Grover's algorithm", revision oldid=1373498442, https://en.wikipedia.org/w/index.php?title=Grover%27s_algorithm&oldid=1373498442, section "Algebraic proof" (PDF p. 6), with section "Geometric proof" (PDF p. 5)

import Mathlib
import Definitions.Def_GroverWiki_Defs

open Matrix

namespace GroverWiki

/-- Stopping at `r = ⌊π/(4t)⌋` iterations, `t = arcsin(1/√N)`, the measurement yields `ω` with
error at most `1/N`. -/
theorem measureProb_groverState_floor {N : ℕ} (f : Fin N → Fin 2) (ω : Fin N)
    (hω : ∀ x, f x = 1 ↔ x = ω) :
    1 - 1 / (N : ℝ) ≤
      measureProb (groverState f ⌊Real.pi / (4 * Real.arcsin (1 / Real.sqrt N))⌋₊) ω := by
  sorry

end GroverWiki
