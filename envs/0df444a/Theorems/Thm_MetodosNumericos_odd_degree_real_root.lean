-- Prove2me | Theorems.Thm_MetodosNumericos_odd_degree_real_root
-- name    : MetodosNumericos.odd_degree_real_root
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T17:08:15.995987+00:00
-- url     : https://prove2.me/theorems/60615d77-ca5a-4031-b1e0-d4aaca8fb5fe
-- title:
--   A real polynomial of odd degree has a real root
-- statement:
--   If a polynomial with real coefficients has odd degree, then it has a real root. This is Proposição 4.1.2, which the source deduces from the conjugate-pair statement and the fundamental theorem of algebra.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 4, Proposição 4.1.2, p. 73.

import Mathlib

namespace MetodosNumericos

theorem odd_degree_real_root (p : Polynomial ℝ) (hodd : Odd p.natDegree) :
    ∃ x : ℝ, p.eval x = 0 := by sorry

end MetodosNumericos
