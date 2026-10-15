-- Prove2me | Theorems.Thm_OAI_ParityWL_coordinate_outside
-- name    : OAI.ParityWL.coordinate_outside
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:44:09.306276+00:00
-- url     : https://prove2.me/theorems/ab793299-d753-4444-bf3a-121d83179a0d
-- title:
--   Three indices never exhaust $\{0,\dots,k-1\}$ when $k\ge4$
-- statement:
--   Let $k\in\mathbb{N}$ and write $[k]=\{0,1,\dots,k-1\}$.
--
--   **Theorem.** If $k\ge4$, then for any three indices $a,b,c\in[k]$ (not necessarily distinct) there is an index different from all of them:
--   $$
--   \exists\, i\in[k]:\qquad i\neq a,\quad i\neq b,\quad i\neq c.
--   $$
--
--   In the analysis of Weisfeiler–Leman colours of $k$-tuples this provides a free coordinate: one can re-sample the $i$-th entry of a tuple while keeping the three entries at positions $a$, $b$, $c$ fixed, and so read off from round-one colours how many vertices are adjacent to all three of them. The bound $k\ge4$ is exactly what is needed for this.
--
--   **Formalization Note** The indices are elements of `Fin k`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/Detection.lean#L48-L60

import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
import Definitions.Def_OAI_Combinatorics_ParityLifts_Witnesses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BagTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_TagSizes
import Definitions.Def_OAI_Combinatorics_ParityLifts_Detection

open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical
variable {V W : Type} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)

theorem OAI.ParityWL.coordinate_outside {k : ℕ} (hk : 4 ≤ k) (a b c : Fin k) :
    ∃ i : Fin k, i ≠ a ∧ i ≠ b ∧ i ≠ c := by sorry
