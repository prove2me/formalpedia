-- Prove2me | Theorems.Thm_MoritaEquiv_thm52_not_morita
-- name    : MoritaEquiv.thm52_not_morita
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-10T13:00:55.658592+00:00
-- url     : https://prove2.me/theorems/f1aba8fa-ce68-444b-aa4a-9fd04abb094f
-- title:
--   Separating example: the two theories are not Morita equivalent
-- statement:
--   The theories $T_1,T_2$ of the separating example are not Morita equivalent: no two finite chains of Morita extensions starting at $T_1$ and $T_2$ end in logically equivalent theories over a common signature (up to renaming).
-- source:
--   T. W. Barrett, H. Halvorson, Morita Equivalence, Rev. Symb. Logic 9 (2016) 556-582, https://arxiv.org/abs/1506.04675 (numbering as in arXiv v1), §5, Theorem 5.2 (second half of the proof)

import Mathlib
import Definitions.Def_MoritaEquiv_defs

open CategoryTheory

namespace MoritaEquiv

/-- Barrett–Halvorson, Theorem 5.2 (second half): the categorically equivalent theories
`Thm52.T1` and `Thm52.T2` are not Morita equivalent. Hence categorical equivalence does not
entail Morita equivalence. -/
theorem thm52_not_morita : ¬ MoritaEquivalent Thm52.T1 Thm52.T2 := by sorry

end MoritaEquiv
