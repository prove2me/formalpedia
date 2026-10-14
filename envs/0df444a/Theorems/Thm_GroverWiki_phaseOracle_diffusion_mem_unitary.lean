-- Prove2me | Theorems.Thm_GroverWiki_phaseOracle_diffusion_mem_unitary
-- name    : GroverWiki.phaseOracle_diffusion_mem_unitary
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T14:34:43.679558+00:00
-- url     : https://prove2.me/theorems/970a0b11-f5d1-4d2d-94ab-eb7a9cdaffc6
-- title:
--   $U_\omega$ and $U_s = 2|s\rangle\langle s| - I$ are unitary
-- statement:
--   Let $f\colon\{0,\dots,N-1\}\to\{0,1\}$, let $U_\omega|x\rangle = (-1)^{f(x)}|x\rangle$ be the phase oracle and let $U_s = 2|s\rangle\langle s| - I$ be the Grover diffusion operator, where $|s\rangle = \frac{1}{\sqrt N}\sum_x|x\rangle$. Then both are unitary:
--
--   $$U_\omega^\dagger U_\omega = U_\omega U_\omega^\dagger = I, \qquad U_s^\dagger U_s = U_sU_s^\dagger = I .$$
--
--   Both steps of a Grover iteration are therefore legitimate quantum operations, and the state of the algorithm stays normalized, so that the measurement probabilities of later milestones are probabilities.
-- source:
--   Wikipedia, "Grover's algorithm", revision oldid=1373498442, https://en.wikipedia.org/w/index.php?title=Grover%27s_algorithm&oldid=1373498442, sections "Problem description" (PDF p. 2) and "Algorithm" / "Geometric proof" (PDF p. 4)

import Mathlib
import Definitions.Def_GroverWiki_Defs

open Matrix

namespace GroverWiki

/-- `U_ω` and `U_s` are unitary operators. -/
theorem phaseOracle_diffusion_mem_unitary {N : ℕ} (f : Fin N → Fin 2) :
    phaseOracle f ∈ unitaryGroup (Fin N) ℂ ∧ diffusion N ∈ unitaryGroup (Fin N) ℂ := by sorry

end GroverWiki
