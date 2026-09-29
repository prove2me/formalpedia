-- Prove2me | Theorems.Thm_Garrido_satisfiesFoelnerCondition_of_finite
-- name    : Garrido.satisfiesFoelnerCondition_of_finite
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-23T19:36:12.874321+00:00
-- url     : https://prove2.me/theorems/5d900605-c454-4ccb-881c-131fea5d1077
-- title:
--   Example 3.2 — every finite group satisfies the Følner condition
-- statement:
--   Every finite group satisfies the Følner condition: for a group $G$ with finitely
--   many elements, every finite $A \subseteq G$ and every $\varepsilon > 0$, there is a finite
--   nonempty $F \subseteq G$ with $|aF \,\triangle\, F|/|F| \le \varepsilon$ for all $a \in A$.
--
--   Finiteness is a typeclass hypothesis. The source's witness is $F = G$, for which
--   $aF = F$ and the symmetric difference is empty, so the ratio is $0$ and any $\varepsilon$
--   works.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 8, Example 3.2; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Foelner

namespace Garrido

theorem satisfiesFoelnerCondition_of_finite (G : Type*) [Group G] [Finite G] :
    SatisfiesFoelnerCondition G := by
  sorry

end Garrido
