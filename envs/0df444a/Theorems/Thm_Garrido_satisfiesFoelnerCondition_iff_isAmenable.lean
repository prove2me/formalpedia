-- Prove2me | Theorems.Thm_Garrido_satisfiesFoelnerCondition_iff_isAmenable
-- name    : Garrido.satisfiesFoelnerCondition_iff_isAmenable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-23T19:40:00.795693+00:00
-- url     : https://prove2.me/theorems/01de44e8-906b-459a-a4ca-34ddb84343ac
-- title:
--   Theorem 3.6 — Følner's theorem
-- statement:
--   For a group $G$: $G$ satisfies the Følner condition if and only if $G$ is
--   amenable.
--
--   Spelled out, the left side is "for every finite $A \subseteq G$ and every real
--   $\varepsilon > 0$ there is a finite nonempty $F \subseteq G$ with
--   $|aF \,\triangle\, F|/|F| \le \varepsilon$ for every $a \in A$", and the right side is "there
--   is a finitely additive left-invariant $m$ on $\mathcal{P}(G)$ with $m(G) = 1$".
--
--   No countability, finiteness or finite-generation hypothesis: the equivalence is for an
--   arbitrary group. This is the mission's goal.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 9, Theorem 3.6; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf. The condition is due to E. Følner, "On groups with full Banach mean value", Math. Scand. 3 (1955), 243–254; https://doi.org/10.7146/math.scand.a-10442. The source proves the converse direction following I. Namioka, "Følner's conditions for amenable semi-groups", Math. Scand. 15 (1964), 18–28; https://doi.org/10.7146/math.scand.a-10723

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Garrido_Foelner

namespace Garrido

theorem satisfiesFoelnerCondition_iff_isAmenable (G : Type*) [Group G] :
    SatisfiesFoelnerCondition G ↔ IsAmenable G := by
  sorry

end Garrido
