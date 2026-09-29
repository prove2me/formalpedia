-- Prove2me | Theorems.Thm_JohnsonApprox_SetCover_lemma1_choosable_iff_selectable
-- name    : JohnsonApprox.SetCover.lemma1_choosable_iff_selectable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:27:13.293891+00:00
-- url     : https://prove2.me/theorems/087df967-f6e5-46dc-a156-23e917a029c1
-- title:
--   Lemma 1 — F₁ is choosable by C1 iff its index set is selectable from the initial configuration
-- statement:
--   Let $F = \{S_i : i \in \iota\}$ be an input of SET COVERING I whose sets $S_i$ are pairwise distinct. Suppose $F_1 \subseteq F$ is a subcover and let
--   $$M1 = \{i : S_i \in F_1\}.$$
--   Let $K$ be the configuration of algorithm C1 after it has been given input $F$ and initialized itself via Step 1. Then
--   $$F_1 \text{ is choosable by C1 given } F \iff M1 \text{ is selectable from } K.$$
--
--   The lemma translates the algorithm's own output (the family SUB it accumulates) into the language of configurations and runs, in which Lemma 2 is proved. Together with Lemma 2 it gives the upper bound of Theorem 4.
--
--   **Formalization Note** Choosability is defined through the algorithm's state (SUB, UNCOV, SET) and selectability through runs of configurations and $\mathrm{Numbers}(R)$, as on p. 266. The paper's family $\{S_1, \dots, S_p\}$ is a set of sets, so its indexing is injective; that is the hypothesis `Function.Injective S`. Without it the identification $M1 = \{i : S_i \in F_1\}$ fails, since a set carried by two indices is chosen only once.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 266, Lemma 1

import Mathlib
import Definitions.Def_JohnsonApprox_SetCover_Problem
import Definitions.Def_JohnsonApprox_SetCover_C1
import Definitions.Def_JohnsonApprox_SetCover_Config

namespace JohnsonApprox.SetCover

theorem lemma1_choosable_iff_selectable {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (S : ι → Finset α) (hS : Function.Injective S)
    (F₁ : Finset (Finset α)) (hF₁ : F₁ ∈ subcovers S) :
    Choosable S F₁ ↔ Selectable (initConfig S) (Finset.univ.filter (fun i => S i ∈ F₁)) := by sorry

end JohnsonApprox.SetCover
