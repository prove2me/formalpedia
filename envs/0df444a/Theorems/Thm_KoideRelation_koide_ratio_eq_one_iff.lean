-- Prove2me | Theorems.Thm_KoideRelation_koide_ratio_eq_one_iff
-- name    : KoideRelation.koide_ratio_eq_one_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T14:28:30.202362+00:00
-- url     : https://prove2.me/theorems/5f381d67-5c78-44b5-9b55-d2e549f9e1c2
-- title:
--   $q = 1$ characterizes a single nonzero mass (Table 3.1)
-- statement:
--   For a nonnegative, not identically zero family of masses, the upper bound $q \le 1$ is attained exactly in the limit of complete hierarchy, i.e. when all masses but one vanish:
--
--   $$ q(m) = 1 \iff \exists\, i,\ \forall j \ne i,\ m_j = 0. $$
--
--   This is the last line of Table 3.1 of the source ($q = 1$, "strong hierarchy", $\psi = \arccos\sqrt{1/3} \approx 54.73^\circ$ for three generations), made exact: the cross terms $2\sqrt{m_i m_j}$ in the denominator vanish precisely when at most one mass is nonzero.
-- source:
--   Goffinet, François, "A bottom-up approach to fermion masses", PhD thesis, Université catholique de Louvain, December 2008, http://hdl.handle.net/2078.1/20873, Chapter 3 "A Mass Relation", pp. 61-63, Table 3.1 (strong hierarchy row: $q = 1$), stated for general $n$

import Definitions.Def_KoideRelation_defs

namespace KoideRelation

theorem koide_ratio_eq_one_iff {n : ℕ} (m : Fin n → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hpos : ∃ i, 0 < m i) :
    koideRatio m = 1 ↔ ∃ i, ∀ j, j ≠ i → m j = 0 := by sorry

end KoideRelation
