-- Prove2me | Theorems.Thm_OAI_OneWayLiveness_Pairing_full_rank_isUnit
-- name    : OAI.OneWayLiveness.Pairing.full_rank_isUnit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:17:23.502475+00:00
-- url     : https://prove2.me/theorems/2a7933ec-a09f-4c8c-ba72-89779eca1a2e
-- title:
--   A matching diagram of full rank is invertible in the diagram monoid
-- statement:
--   Let $A$ be a finite set and let $\mathcal P(A)$ be the monoid of diagrams on $A$. Its elements are perfect matchings of $A\sqcup A$, a left and a right copy of $A$. The product glues the right copy of the first diagram to the left copy of the second, follows paths and discards closed loops. The identity matches each left $i$ with the right $i$. The *rank* of $a\in\mathcal P(A)$ is the number of left ports that $a$ matches to right ports, i.e. its number of through-strands.
--
--   **Theorem.** If $\operatorname{rank}(a)=|A|$, then $a$ is a unit of $\mathcal P(A)$:
--   $$
--   \operatorname{rank}(a)=|A|\quad\Longrightarrow\quad\exists\,b\in\mathcal P(A):\ \ ab=ba=1 .
--   $$
--
--   A diagram of full rank has no caps, so it is the diagram of a permutation of $A$. The theorem converts full rank into invertibility. In the rank-loss argument it is used to show that a reduced corner element of full rank is a unit, and that an idempotent of full rank is trivial.
--
--   **Formalization Note** The diagram monoid is `Pairing (A ⊕ A)` with multiplication `compose` and identity `identity A`, and the conclusion is `IsUnit a`. The rank is `Pairing.rank a`, the cardinality of the `Finset` `lefts a` of left endpoints of through-strands, and $|A|$ is `Fintype.card A`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Diagram.lean#L158-L170

import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization
import Definitions.Def_OAI_Combinatorics_Automata_Network
import Definitions.Def_OAI_Combinatorics_Automata_Rank
import Definitions.Def_OAI_Combinatorics_Automata_Diagram

open OAI OAI.OneWayLiveness OAI.OneWayLiveness.Pairing
open scoped Classical
variable {A : Type*} [Fintype A]

theorem OAI.OneWayLiveness.Pairing.full_rank_isUnit (a : Pairing (A ⊕ A)) (h : rank a = Fintype.card A) : IsUnit a := by sorry
