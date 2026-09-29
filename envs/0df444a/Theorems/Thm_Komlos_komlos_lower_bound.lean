-- Prove2me | Theorems.Thm_Komlos_komlos_lower_bound
-- name    : Komlos.komlos_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-03T20:54:21.305984+00:00
-- url     : https://prove2.me/theorems/3af3ddce-cb1a-4fb7-b3b6-a78a3e0e64e5
-- title:
--   Kunisky: the Komlós constant is at least $1+\sqrt{2}$
-- statement:
--   (Kunisky 2023.) Any constant $K$ with the Komlós property satisfies $K \ge 1 + \sqrt{2} \approx 2.414$. Kunisky constructs explicit families of unit-norm columns — scaled clause-variable matrices of unsatisfiable Boolean formulas — whose discrepancy under every signing approaches $1+\sqrt{2}$; consequently no smaller universal constant can work. This is the strongest known lower bound on the conjectured constant (the conjecture itself asserts some finite $K$ suffices).
-- source:
--   Kunisky, The discrepancy of unsatisfiable matrices and a lower bound for the Komlos conjecture constant, SIAM J. Discrete Math. 37 (2023), main theorem, https://arxiv.org/abs/2111.02974

import Mathlib
import Definitions.Def_Komlos_model

namespace Komlos

theorem komlos_lower_bound (K : ℝ) (hK : KomlosBound K) :
    1 + Real.sqrt 2 ≤ K := by sorry

end Komlos
