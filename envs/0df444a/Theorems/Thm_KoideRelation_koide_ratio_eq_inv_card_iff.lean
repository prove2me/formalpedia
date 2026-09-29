-- Prove2me | Theorems.Thm_KoideRelation_koide_ratio_eq_inv_card_iff
-- name    : KoideRelation.koide_ratio_eq_inv_card_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T14:23:11.331177+00:00
-- url     : https://prove2.me/theorems/f2d20ad9-500e-423d-bfb6-099bd41d15de
-- title:
--   $q = \tfrac1n$ characterizes complete degeneracy (Table 3.1)
-- statement:
--   For a nonnegative, not identically zero family of $n$ masses, the lower bound of the previous milestone is attained exactly at complete degeneracy:
--
--   $$ q(m) = \frac1n \iff m_1 = m_2 = \dots = m_n. $$
--
--   This is the first line of Table 3.1 of the source ($q = \tfrac13$, $\psi = 0$ for three degenerate masses), stated as an exact characterization: it is the equality case of Cauchy–Schwarz for the vectors $(\sqrt{m_i})_i$ and $(1,\dots,1)$.
-- source:
--   Goffinet, François, "A bottom-up approach to fermion masses", PhD thesis, Université catholique de Louvain, December 2008, http://hdl.handle.net/2078.1/20873, Chapter 3 "A Mass Relation", pp. 61-63, Table 3.1 (degeneracy row: $q = 1/3$, $\psi = 0$), stated for general $n$

import Definitions.Def_KoideRelation_defs

namespace KoideRelation

theorem koide_ratio_eq_inv_card_iff {n : ℕ} (m : Fin n → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hpos : ∃ i, 0 < m i) :
    koideRatio m = 1 / (n : ℝ) ↔ ∀ i j, m i = m j := by sorry

end KoideRelation
