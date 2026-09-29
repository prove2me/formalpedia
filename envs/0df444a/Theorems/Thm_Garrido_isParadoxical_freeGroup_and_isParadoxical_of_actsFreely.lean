-- Prove2me | Theorems.Thm_Garrido_isParadoxical_freeGroup_and_isParadoxical_of_actsFreely
-- name    : Garrido.isParadoxical_freeGroup_and_isParadoxical_of_actsFreely
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-24T13:59:19.652486+00:00
-- url     : https://prove2.me/theorems/f85b3c02-2f52-4e46-a3c5-9d2667dcc9e9
-- title:
--   Proposition 1.5 — the free group of rank two is paradoxical, and so is every set it acts on freely
-- statement:
--   Let $F_2$ be the free group on two generators. Then $F_2$ is $F_2$-paradoxical for
--   its action on itself by left multiplication; and whenever $F_2$ acts freely on a nonempty set
--   $X$, the whole of $X$ is $F_2$-paradoxical:
--
--   $$F_2 \text{ is } F_2\text{-paradoxical}, \qquad F_2 \curvearrowright X \text{ free},\ X \neq \emptyset \implies X \text{ is } F_2\text{-paradoxical}.$$
--
--   The first part is the combinatorial heart of the Banach–Tarski paradox; the second transports
--   it to any set on which $F_2$ acts without fixed points, which is how it reaches the sphere.
--
--   **Formalization Note.** $F_2$ is `FreeGroup (Fin 2)`. Paradoxicality is the imported
--   `IsParadoxical`, applied to the whole set. The second part assumes $X$ nonempty, which the
--   source's sentence does not state: the empty set carries a free action and is not paradoxical, so
--   without it the statement would be false. $X$ ranges over types in an arbitrary universe.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 2, Proposition 1.5; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_BanachTarski
import Definitions.Def_Garrido_Equidecomposability
universe u

namespace Garrido

theorem isParadoxical_freeGroup_and_isParadoxical_of_actsFreely :
    IsParadoxical (FreeGroup (Fin 2)) (Set.univ : Set (FreeGroup (Fin 2))) ∧
      ∀ (X : Type u) [MulAction (FreeGroup (Fin 2)) X] [Nonempty X],
        ActsFreely (FreeGroup (Fin 2)) X → IsParadoxical (FreeGroup (Fin 2)) (Set.univ : Set X) := by
  sorry

end Garrido
