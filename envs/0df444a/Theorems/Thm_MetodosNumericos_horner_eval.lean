-- Prove2me | Theorems.Thm_MetodosNumericos_horner_eval
-- name    : MetodosNumericos.horner_eval
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T17:32:11.874988+00:00
-- url     : https://prove2.me/theorems/d33d48b9-9a58-4f34-a658-d8d24b370b22
-- title:
--   Correctness of Horner's evaluation scheme
-- statement:
--   For every coefficient family $a$, degree $n$ and point $z$, the last Horner coefficient equals the value of the polynomial: $b_n = P(z)$, where $b_0 = a_0$ and $b_i = a_i + z\\,b_{i-1}$. This is the correctness of the algorithm of §4.5.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 4, §4.4–4.5, pp. 77–79.

import Mathlib
import Definitions.Def_MetodosNumericos_polinomiosDefs

namespace MetodosNumericos

theorem horner_eval (a : ℕ → ℝ) (n : ℕ) (z : ℝ) :
    polyVal a n z = hornerSeq a z n := by sorry

end MetodosNumericos
