-- Prove2me | Theorems.Thm_Garrido_not_isParadoxical_of_isExponentiallyBounded
-- name    : Garrido.not_isParadoxical_of_isExponentiallyBounded
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-23T19:44:49.571134+00:00
-- url     : https://prove2.me/theorems/9b41dfb4-810d-4149-9ce3-61251a3de9a5
-- title:
--   Theorem 3.10(1) — no nonempty subset is paradoxical under a subexponential group
-- statement:
--   Let $G$ be a group of subexponential growth acting on a set $X$. Then no
--   nonempty $A \subseteq X$ is $G$-paradoxical.
--
--   Subexponential growth is the published `Chou.IsExponentiallyBounded`, which also carries finite
--   generation. The conclusion is for every nonempty subset of $X$, not merely for $X$ itself. The
--   restriction to nonempty subsets follows the source and costs nothing: under the mission's
--   definition the empty set is never paradoxical.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 11, Theorem 3.10(1); https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Equidecomposability
import Definitions.Def_Chou_Growth

namespace Garrido

theorem not_isParadoxical_of_isExponentiallyBounded {G : Type*} [Group G]
    (hG : Chou.IsExponentiallyBounded G) {X : Type*} [MulAction G X]
    (A : Set X) (hA : A.Nonempty) :
    ¬ IsParadoxical G A := by
  sorry

end Garrido
