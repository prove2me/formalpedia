-- Prove2me | Theorems.Thm_KontsevichHMS_ainf_dg_of_vanishing_higher
-- name    : KontsevichHMS.ainf_dg_of_vanishing_higher
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T02:58:40.04007+00:00
-- url     : https://prove2.me/theorems/7bfb0900-1eff-4925-9780-ce7e89f7ca15
-- title:
--   An $A_\infty$-category with $m_{\ge 3} = 0$ is a dg-category
-- statement:
--   Kontsevich observes on p. 14 that a differential graded algebra is the same thing as an $A_\infty$-algebra with $m_3 = m_4 = \cdots = 0$, and likewise for categories. The milestone makes the observation precise in one direction: if all compositions of arity at least three vanish, then the Stasheff identities reduce to the two dg-axioms, namely that $m_1$ is a derivation for $m_2$,
--   $$m_1(m_2(a,b)) = m_2(m_1 a, b) + m_2(a, m_1 b),$$
--   and that $m_2$ is strictly associative,
--   $$m_2(m_2(a,b),c) = m_2(a, m_2(b,c)).$$
--   The first identity is a consequence of the arity-two Stasheff relation alone; the second uses the vanishing of $m_3$ in the arity-three relation.
-- source:
--   M. Kontsevich, Homological algebra of mirror symmetry, Proc. ICM Zurich 1994, arXiv:alg-geom/9411018, p. 14 ('a dg-algebra is the same as an A-infinity-algebra with m3 = m4 = ... = 0')

import Mathlib
import Definitions.Def_KontsevichHMS_AInfCategory

universe u

namespace KontsevichHMS

/-- An A∞-category with `m₃ = m₄ = ⋯ = 0` is a differential graded category: `m₁` is a
derivation for `m₂`, and `m₂` is associative on the nose. -/
theorem ainf_dg_of_vanishing_higher (C : AInfCategory.{u} ℂ)
    (hhigh : ∀ L : List C.A, 3 ≤ L.length → C.m L = 0) :
    (∀ a b : C.A, C.m [C.m [a, b]] = C.m [C.m [a], b] + C.m [a, C.m [b]]) ∧
      ∀ a b c : C.A, C.m [C.m [a, b], c] = C.m [a, C.m [b, c]] := by sorry

end KontsevichHMS
