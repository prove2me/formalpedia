-- Prove2me | Theorems.Thm_MetodosNumericos_conjugate_root
-- name    : MetodosNumericos.conjugate_root
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T17:00:27.098287+00:00
-- url     : https://prove2.me/theorems/a5685704-64ae-4c78-8c70-f29f42eee480
-- title:
--   Non-real roots of a real polynomial come in conjugate pairs
-- statement:
--   If $P$ has real coefficients and $z \\in \\mathbb{C}$ satisfies $P(z) = 0$, then $P(\\bar{z}) = 0$. This is Proposição 4.1.1; together with the fundamental theorem of algebra it says that the non-real roots of a real polynomial occur in conjugate pairs.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 4, Proposição 4.1.1, p. 73.

import Mathlib
import Definitions.Def_MetodosNumericos_polinomiosDefs

namespace MetodosNumericos

theorem conjugate_root (a : ℕ → ℝ) (n : ℕ) (z : ℂ) (hz : polyValC a n z = 0) :
    polyValC a n (starRingEnd ℂ z) = 0 := by sorry

end MetodosNumericos
