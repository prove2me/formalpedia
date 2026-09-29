-- Prove2me | Theorems.Thm_KoideRelation_koide_matrix_form
-- name    : KoideRelation.koide_matrix_form
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T14:45:56.27637+00:00
-- url     : https://prove2.me/theorems/79be2fed-fcd9-4325-8bce-0e3d66e4a7ea
-- title:
--   Matrix form of the square-root-free relation (eq. 3.30)
-- statement:
--   Let $M$ be a $3\times3$ Hermitian mass matrix with nonnegative eigenvalues $m_1, m_2, m_3$. Since
--
--   $$ \operatorname{tr} M = \sum_i m_i, \qquad \operatorname{tr}(M^2) = \sum_i m_i^2, \qquad \det M = m_1m_2m_3, $$
--
--   the elementary symmetric functions appearing in (3.24) are expressible through traces and the determinant, and Koide's relation for the eigenvalues implies the basis-independent identity
--
--   $$ \Big[7\,(\operatorname{tr} M)^2 - 8\,\operatorname{tr}(M^2)\Big]^2 = \tfrac32\cdot 32^2\,\det(M)\,\operatorname{tr}(M), $$
--
--   which is equation (3.30) of the source. This is the form in which the relation can be imposed on a mass matrix without ever extracting eigenvalues or square roots.
-- source:
--   Goffinet, François, "A bottom-up approach to fermion masses", PhD thesis, Université catholique de Louvain, December 2008, http://hdl.handle.net/2078.1/20873, Chapter 3 "A Mass Relation", p. 72, eq. (3.30), with the Hermitian assumption stated on p. 71

import Definitions.Def_KoideRelation_defs

namespace KoideRelation

theorem koide_matrix_form (M : Matrix (Fin 3) (Fin 3) ℂ) (hM : M.IsHermitian)
    (hpos : ∀ i, 0 ≤ hM.eigenvalues i) (hq : koideRatio hM.eigenvalues = 2 / 3) :
    (7 * M.trace ^ 2 - 8 * (M * M).trace) ^ 2 = 3 / 2 * 32 ^ 2 * M.det * M.trace := by sorry

end KoideRelation
