-- Prove2me | Theorems.Thm_Monod_exists_biInvariant_linearOrder_Hpp
-- name    : Monod.exists_biInvariant_linearOrder_Hpp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-30T13:27:59.130297+00:00
-- url     : https://prove2.me/theorems/af64c400-03fa-4bd9-8599-071eee9badc2
-- title:
--   Proposition 6 — H and all its subgroups are bi-orderable
-- statement:
--   $H$ carries a linear order invariant under multiplication on both sides ($a \le b \Rightarrow ca \le cb$ and $ac \le bc$), and so does every subgroup of $H$.
--
--   **Formalization Note.** The source's second sentence of Proposition 6 (no non-trivial homomorphism from a Kazhdan group) is not formalized: property (T) is not in Mathlib.
-- source:
--   Monod, N., Groups of piecewise projective homeomorphisms, Proc. Natl. Acad. Sci. USA 110 (2013) 4524–4527, https://doi.org/10.1073/pnas.1218426110 (arXiv:1209.5229v2, whose page numbers are used), p. 1, Proposition 6

import Mathlib
import Definitions.Def_Monod_PiecewiseProjective

namespace Monod

theorem exists_biInvariant_linearOrder_Hpp :
    (∃ r : LinearOrder Hpp, ∀ a b c : Hpp, r.le a b → r.le (c * a) (c * b) ∧ r.le (a * c) (b * c)) ∧
      ∀ K : Subgroup Hpp, ∃ r : LinearOrder K,
        ∀ a b c : K, r.le a b → r.le (c * a) (c * b) ∧ r.le (a * c) (b * c) := by
  sorry

end Monod
