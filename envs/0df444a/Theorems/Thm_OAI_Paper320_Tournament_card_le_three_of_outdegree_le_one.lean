-- Prove2me | Theorems.Thm_OAI_Paper320_Tournament_card_le_three_of_outdegree_le_one
-- name    : OAI.Paper320.Tournament.card_le_three_of_outdegree_le_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:01:51.35123+00:00
-- url     : https://prove2.me/theorems/9af9fb37-d63b-44bf-afb7-0a9f45b14b9f
-- title:
--   A vertex set of a tournament with internal out-degrees at most one has at most three vertices
-- statement:
--   Let $T$ be a tournament on $[k] = \{0, \dots, k-1\}$ with edge relation $i \to j$ (no loops, and every two distinct vertices joined in exactly one direction). Let $I \subseteq [k]$ be a set of vertices in which every vertex has at most one out-neighbour inside $I$:
--   $$
--   |\{ j \in I : i \to j \}| \le 1 \qquad \text{for every } i \in I .
--   $$
--   Then
--   $$
--   |I| \le 3 .
--   $$
--
--   The bound is attained by a directed triangle. In the row-clause construction separating block sensitivity from sensitivity, applied to a nested family, every gate-candidate row has at most one out-neighbour among the gate candidates, so this lemma shows that there are at most three gate candidates; this is the source of the factor $3$ in the recurrences for sensitivity on rejected inputs.
--
--   **Formalization Note** The hypothesis is `∀ i ∈ I, (I.filter (T.Adj i)).card ≤ 1`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/TournamentCounts.lean#L51-L63

import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tournament
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveDefinitions
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveBlocks
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveSets
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCounts

open OAI OAI.Paper320 OAI.Paper320.Tournament
open scoped Classical BigOperators
variable {k : ℕ} (T : Tournament k)

theorem OAI.Paper320.Tournament.card_le_three_of_outdegree_le_one (I : Finset (Fin k))
    (h : ∀ i ∈ I, (I.filter (T.Adj i)).card ≤ 1) : I.card ≤ 3 := by sorry
