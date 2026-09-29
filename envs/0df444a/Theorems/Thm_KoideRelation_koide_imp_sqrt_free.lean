-- Prove2me | Theorems.Thm_KoideRelation_koide_imp_sqrt_free
-- name    : KoideRelation.koide_imp_sqrt_free
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T14:39:46.445123+00:00
-- url     : https://prove2.me/theorems/b93b663c-1f4e-4763-a340-bfa1c26a1ef8
-- title:
--   Square-root-free consequence of Koide's relation (eq. 3.24)
-- statement:
--   Square roots of masses are awkward for model building, and the source eliminates them by squaring Koide's relation twice. The result is that any nonnegative triple satisfying $q = \tfrac23$ also satisfies the polynomial identity
--
--   $$ \Big((m_1+m_2+m_3)^2 - 16\,(m_1m_2 + m_2m_3 + m_1m_3)\Big)^2 = \tfrac{3}{2}\cdot 32^2\; m_1m_2m_3\,(m_1+m_2+m_3). $$
--
--   This is equation (3.24). Only the forward implication is asserted — and indeed the converse is false, as the counterexample milestone shows.
-- source:
--   Goffinet, François, "A bottom-up approach to fermion masses", PhD thesis, Université catholique de Louvain, December 2008, http://hdl.handle.net/2078.1/20873, Chapter 3 "A Mass Relation", pp. 70-71, eq. (3.24)

import Definitions.Def_KoideRelation_defs

namespace KoideRelation

theorem koide_imp_sqrt_free (m₁ m₂ m₃ : ℝ) (h₁ : 0 ≤ m₁) (h₂ : 0 ≤ m₂) (h₃ : 0 ≤ m₃)
    (hq : koideRatio ![m₁, m₂, m₃] = 2 / 3) :
    ((m₁ + m₂ + m₃) ^ 2 - 16 * (m₁ * m₂ + m₂ * m₃ + m₁ * m₃)) ^ 2
      = 3 / 2 * 32 ^ 2 * (m₁ * m₂ * m₃) * (m₁ + m₂ + m₃) := by sorry

end KoideRelation
