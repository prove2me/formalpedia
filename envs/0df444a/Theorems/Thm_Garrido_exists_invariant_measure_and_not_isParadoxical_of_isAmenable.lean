-- Prove2me | Theorems.Thm_Garrido_exists_invariant_measure_and_not_isParadoxical_of_isAmenable
-- name    : Garrido.exists_invariant_measure_and_not_isParadoxical_of_isAmenable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-23T19:10:22.077929+00:00
-- url     : https://prove2.me/theorems/a8a79e4f-e821-44d4-bb13-9e842085151b
-- title:
--   Proposition 1.14 — under an amenable group, a nonempty set carries an invariant probability measure and is not paradoxical
-- statement:
--   Let $G$ be an amenable group acting on a **nonempty** set $X$. Then both:
--
--   - there is a finitely additive $G$-invariant $m : \mathcal{P}(X) \to [0,\infty]$ with
--     $m(X) = 1$; and
--   - $X$ is not $G$-paradoxical.
--
--   Both conclusions are asserted, matching the source, whose statement ends "Therefore
--   $X$ is not $G$-paradoxical (by Tarski's theorem)".
--
--   The nonemptiness of $X$ is a hypothesis here although the source leaves it implicit — its proof
--   begins "Choose a point $x \in X$". It cannot be dropped: for $X = \emptyset$ we would need
--   $m(\emptyset) = 1$, while a finitely additive measure has $m(\emptyset) = 0$, so the statement would
--   be false rather than merely unprovable.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 5, Proposition 1.14; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Equidecomposability
import Definitions.Def_Garrido_Amenability
open scoped ENNReal

namespace Garrido

theorem exists_invariant_measure_and_not_isParadoxical_of_isAmenable
    {G : Type*} [Group G] (hG : IsAmenable G)
    (X : Type*) [MulAction G X] [Nonempty X] :
    (∃ m : Set X → ℝ≥0∞, IsFinitelyAdditiveMeasure m ∧ m Set.univ = 1 ∧
        IsInvariant G m) ∧
      ¬ IsParadoxical G (Set.univ : Set X) := by
  sorry

end Garrido
