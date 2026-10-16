-- Prove2me | Theorems.Thm_GroverWiki_measureProb_groverState
-- name    : GroverWiki.measureProb_groverState
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T14:40:08.785368+00:00
-- url     : https://prove2.me/theorems/61a26305-98ba-4fe9-b01e-57b59cfa0008
-- title:
--   Exact success probability after $r$ iterations: $\sin^2((r+\frac12)\theta)$
-- statement:
--   Let $f\colon\{0,\dots,N-1\}\to\{0,1\}$ have exactly one index $\omega$ with $f(\omega) = 1$, and let $\theta = 2\arcsin\frac{1}{\sqrt N}$. Starting from $|s\rangle$ and applying $r$ Grover iterations, the probability that a computational-basis measurement of $(U_sU_\omega)^r|s\rangle$ yields $\omega$ is exactly
--
--   $$\bigl|\langle\omega|(U_sU_\omega)^r|s\rangle\bigr|^2 = \sin^2\!\Bigl(\bigl(r+\tfrac12\bigr)\theta\Bigr) .$$
--
--   This is the central quantitative statement about Grover's algorithm: the success probability oscillates with the number of iterations and is close to $1$ when $(r+\frac12)\theta \approx \pi/2$.
-- source:
--   Wikipedia, "Grover's algorithm", revision oldid=1373498442, https://en.wikipedia.org/w/index.php?title=Grover%27s_algorithm&oldid=1373498442, section "Geometric proof" (PDF p. 5)

import Mathlib
import Definitions.Def_GroverWiki_Defs

open Matrix

namespace GroverWiki

/-- Geometric proof: the exact probability of measuring `ω` after `r` Grover iterations is
`sin²((r + 1/2) θ)` with `θ = 2 arcsin(1/√N)`. -/
theorem measureProb_groverState {N : ℕ} (f : Fin N → Fin 2) (ω : Fin N)
    (hω : ∀ x, f x = 1 ↔ x = ω) (r : ℕ) :
    measureProb (groverState f r) ω =
      Real.sin ((r + 1 / 2) * (2 * Real.arcsin (1 / Real.sqrt N))) ^ 2 := by sorry

end GroverWiki
