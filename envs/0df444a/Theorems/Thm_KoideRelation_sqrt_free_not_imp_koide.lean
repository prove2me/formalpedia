-- Prove2me | Theorems.Thm_KoideRelation_sqrt_free_not_imp_koide
-- name    : KoideRelation.sqrt_free_not_imp_koide
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T14:51:53.41955+00:00
-- url     : https://prove2.me/theorems/ca05aaf1-6d60-4f65-9f68-b3dc0196f3d4
-- title:
--   The square-root-free relation is strictly weaker (eqs. 3.26-3.28)
-- statement:
--   Squaring twice is not reversible, so the polynomial relation (3.24) has solutions that Koide's relation does not: the source records them in equations (3.26)–(3.28) as the extra branch $m_3 = 7(m_1+m_2) - 20\sqrt{m_1m_2} \pm 4\sqrt3\,|\sqrt{m_1}-\sqrt{m_2}|\sqrt{m_1 - 4\sqrt{m_1m_2} + m_2}$, real only when $m_2 \ge (7+4\sqrt3)\,m_1$ or $m_2 \le (7-4\sqrt3)\,m_1$. The milestone asks for a witness: a triple of strictly positive masses satisfying the polynomial identity of (3.24) but **not** $q = \tfrac23$. An explicit one is
--
--   $$ (m_1, m_2, m_3) = \left(1,\; 16,\; 39 + 12\sqrt3\right), \qquad q \approx 0.4737, $$
--
--   for which both sides of (3.24) equal $64290816 + 28016640\sqrt3$. This is the precise sense in which the square-root-free rewriting loses information.
-- source:
--   Goffinet, François, "A bottom-up approach to fermion masses", PhD thesis, Université catholique de Louvain, December 2008, http://hdl.handle.net/2078.1/20873, Chapter 3 "A Mass Relation", pp. 71-72, eqs. (3.26)-(3.28) and the surrounding discussion of the two extra solutions

import Definitions.Def_KoideRelation_defs

namespace KoideRelation

theorem sqrt_free_not_imp_koide :
    ∃ m : Fin 3 → ℝ, (∀ i, 0 < m i) ∧
      ((m 0 + m 1 + m 2) ^ 2 - 16 * (m 0 * m 1 + m 1 * m 2 + m 0 * m 2)) ^ 2
        = 3 / 2 * 32 ^ 2 * (m 0 * m 1 * m 2) * (m 0 + m 1 + m 2) ∧
      koideRatio m ≠ 2 / 3 := by sorry

end KoideRelation
