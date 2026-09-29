-- Prove2me | Theorems.Thm_KontsevichHMS_ainf_cohomology_associative
-- name    : KontsevichHMS.ainf_cohomology_associative
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T02:53:21.923768+00:00
-- url     : https://prove2.me/theorems/c6628d0f-efd2-4c36-a08a-6ff5f3a19bf6
-- title:
--   $m_1$ is a differential and $m_2$ is associative up to coboundary
-- statement:
--   Kontsevich lists the first Stasheff relations as: $m_1^2 = 0$, so that $(A, m_1)$ is a complex; $m_2$ is a morphism of complexes; and $m_2$ is associative up to a homotopy given by $m_3$. These are what allow him to build from an $A_\infty$-category $C$ an ordinary additive category $H(C)$, whose morphisms are the $m_1$-cohomology classes and whose composition is induced by $m_2$ (pp. 14--15).
--
--   The milestone extracts the two facts that make this construction work, for an arbitrary $A_\infty$-category over $\mathbb{C}$: first, $m_1 \circ m_1 = 0$; second, for any three $m_1$-closed morphisms $a, b, c$ the associator $m_2(m_2(a,b),c) - m_2(a,m_2(b,c))$ is an $m_1$-coboundary. Together they say that $m_2$ descends to an associative composition on $m_1$-cohomology.
-- source:
--   M. Kontsevich, Homological algebra of mirror symmetry, Proc. ICM Zurich 1994, arXiv:alg-geom/9411018, pp. 13-15, relations (1)-(4) and the construction of the category H(C)

import Mathlib
import Definitions.Def_KontsevichHMS_AInfCategory

universe u

namespace KontsevichHMS

/-- `m₁` is a differential and `m₂` is associative up to `m₁`-coboundaries. -/
theorem ainf_cohomology_associative (C : AInfCategory.{u} ℂ) :
    (∀ a : C.A, C.m [C.m [a]] = 0) ∧
      ∀ a b c : C.A, C.m [a] = 0 → C.m [b] = 0 → C.m [c] = 0 →
        ∃ h : C.A, C.m [C.m [a, b], c] - C.m [a, C.m [b, c]] = C.m [h] := by sorry

end KontsevichHMS
