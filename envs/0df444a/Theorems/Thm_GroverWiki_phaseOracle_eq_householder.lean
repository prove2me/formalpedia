-- Prove2me | Theorems.Thm_GroverWiki_phaseOracle_eq_householder
-- name    : GroverWiki.phaseOracle_eq_householder
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T14:36:50.346484+00:00
-- url     : https://prove2.me/theorems/abdf5418-cfd4-4147-be18-45ae16b3981e
-- title:
--   Householder form of the oracle: $U_\omega = I - 2|\omega\rangle\langle\omega|$
-- statement:
--   Let $f\colon\{0,\dots,N-1\}\to\{0,1\}$ have exactly one index $\omega$ with $f(\omega) = 1$, and let $U_\omega|x\rangle = (-1)^{f(x)}|x\rangle$ be the phase oracle. Then $U_\omega$ is the Householder reflection
--
--   $$U_\omega = I - 2|\omega\rangle\langle\omega| .$$
--
--   This identifies the oracle as a reflection, the first ingredient of the geometric picture of Grover's algorithm.
-- source:
--   Wikipedia, "Grover's algorithm", revision oldid=1373498442, https://en.wikipedia.org/w/index.php?title=Grover%27s_algorithm&oldid=1373498442, section "Geometric proof" (PDF p. 4)

import Mathlib
import Definitions.Def_GroverWiki_Defs

open Matrix

namespace GroverWiki

/-- Householder form of the oracle: if `ω` is the unique index with `f(ω) = 1`, then
`U_ω = I - 2|ω⟩⟨ω|`. -/
theorem phaseOracle_eq_householder {N : ℕ} (f : Fin N → Fin 2) (ω : Fin N)
    (hω : ∀ x, f x = 1 ↔ x = ω) :
    phaseOracle f = 1 - (2 : ℂ) • vecMulVec (ket ω) (star (ket ω)) := by sorry

end GroverWiki
