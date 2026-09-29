-- Prove2me | Theorems.Thm_KoideRelation_koide_third_mass_solutions
-- name    : KoideRelation.koide_third_mass_solutions
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T15:13:42.345615+00:00
-- url     : https://prove2.me/theorems/4f81c6cf-6ede-4eb0-ba20-8093e74c2719
-- title:
--   Exact solution of $q = \tfrac23$ for the third mass (eq. 3.25)
-- statement:
--   Fix two positive masses $m_1, m_2$ and let $m_3 > 0$. Write $P = \sqrt{m_1 m_2}$ and $R = \sqrt{m_1 + 4P + m_2}$. Then Koide's relation
--
--   $$ m_1 + m_2 + m_3 = \tfrac{2}{3}\left(\sqrt{m_1}+\sqrt{m_2}+\sqrt{m_3}\right)^2, \qquad\text{i.e.}\qquad q(m_1,m_2,m_3) = \tfrac{2}{3},$$
--
--   holds if and only if
--
--   $$ m_3 = 7(m_1+m_2) + 20P + 4\sqrt{3}\,(\sqrt{m_1}+\sqrt{m_2})\,R $$
--
--   or
--
--   $$ 4P < m_1 + m_2 \quad\text{and}\quad m_3 = 7(m_1+m_2) + 20P - 4\sqrt{3}\,(\sqrt{m_1}+\sqrt{m_2})\,R. $$
--
--   This is equation (3.25) of the source, with the admissibility of the lower branch made explicit. Setting $x = \sqrt{m_1}$, $y = \sqrt{m_2}$, $z = \sqrt{m_3}$, the relation is the quadratic $z^2 - 4(x+y)z + (x^2 - 4xy + y^2) = 0$, whose roots are $z_\pm = 2(x+y) \pm \sqrt{3}\sqrt{x^2+4xy+y^2}$; squaring gives the two displayed values of $m_3$. The root $z_-$ is positive exactly when $x^2 + y^2 > 4xy$, i.e. when $m_1 + m_2 > 4\sqrt{m_1 m_2}$, and only then does the corresponding value of $m_3$ satisfy the original relation. The source's phrasing that (3.1) "has only two solutions for the third mass" is therefore correct only under that inequality; for instance at $m_1 = m_2$ the "$-$" value of $m_3$ is positive but does **not** satisfy $q = \tfrac23$.
-- source:
--   Goffinet, François, "A bottom-up approach to fermion masses", PhD thesis, Université catholique de Louvain, December 2008, http://hdl.handle.net/2078.1/20873, Chapter 3 "A Mass Relation", p. 71, eq. (3.25) (admissibility condition for the lower branch made explicit)

import Definitions.Def_KoideRelation_defs

namespace KoideRelation

theorem koide_third_mass_solutions (m₁ m₂ m₃ : ℝ) (h₁ : 0 < m₁) (h₂ : 0 < m₂) (h₃ : 0 < m₃) :
    koideRatio ![m₁, m₂, m₃] = 2 / 3 ↔
      m₃ = 7 * (m₁ + m₂) + 20 * Real.sqrt (m₁ * m₂)
            + 4 * Real.sqrt 3 * (Real.sqrt m₁ + Real.sqrt m₂)
              * Real.sqrt (m₁ + 4 * Real.sqrt (m₁ * m₂) + m₂) ∨
      (4 * Real.sqrt (m₁ * m₂) < m₁ + m₂ ∧
        m₃ = 7 * (m₁ + m₂) + 20 * Real.sqrt (m₁ * m₂)
              - 4 * Real.sqrt 3 * (Real.sqrt m₁ + Real.sqrt m₂)
                * Real.sqrt (m₁ + 4 * Real.sqrt (m₁ * m₂) + m₂)) := by sorry

end KoideRelation
