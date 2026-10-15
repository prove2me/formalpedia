-- Prove2me | Theorems.Thm_OAI_Paper320_Tournament_card_internalEdges
-- name    : OAI.Paper320.Tournament.card_internalEdges
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:01:27.247603+00:00
-- url     : https://prove2.me/theorems/181421f6-6690-4099-ade6-387b7115171a
-- title:
--   A set of $n$ vertices of a tournament spans exactly $\binom{n}{2}$ edges
-- statement:
--   Let $T$ be a tournament on $[k] = \{0, \dots, k-1\}$: a directed graph with edge relation $i \to j$, without loops, in which every two distinct vertices are joined in exactly one direction. For a set of vertices $I \subseteq [k]$, the internal edges of $I$ are the ordered pairs
--   $$
--   E_T(I) = \{ (i,j) \in I \times I : i \to j \}.
--   $$
--   Then
--   $$
--   |E_T(I)| = \binom{|I|}{2} .
--   $$
--
--   Thus every set of $n$ vertices spans exactly $\binom{n}{2}$ edges, whatever the orientations. This count determines how many labels are constrained when a labeling is required to be target-constant on an $n$-vertex set ($120$ labels for $n = 16$), and, combined with a sum of out-degrees, it shows that a vertex set in which every vertex has at most one out-neighbour inside the set has at most three vertices.
--
--   **Formalization Note** `T.internalEdges I` is the filter of `I ×ˢ I` by `T.Adj`, and the right-hand side is `I.card.choose 2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/TournamentCounts.lean#L19-L45

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

theorem OAI.Paper320.Tournament.card_internalEdges (I : Finset (Fin k)) :
    (T.internalEdges I).card = I.card.choose 2 := by sorry
