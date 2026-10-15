-- Prove2me | Theorems.Thm_OAI_ParityWL_template_positive_degree
-- name    : OAI.ParityWL.template_positive_degree
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:43:42.471835+00:00
-- url     : https://prove2.me/theorems/8c2095a0-bf4b-4a76-b49a-4b9cd8a15339
-- title:
--   Every vertex of the template graph $T_t$ has a neighbour when $t\ge 2$
-- statement:
--   Let $t\in\mathbb{N}$. The *template graph* $T_t$ has vertex set $[t]\sqcup\mathcal{H}_t$, where $[t]=\{0,1,\dots,t-1\}$ is the set of *main vertices* and $\mathcal{H}_t$ is the set of *helper vertices* $h=(i,j;m)$ with $i<j$ in $[t]$ and $m\in[t]\setminus\{i,j\}$. Any two distinct main vertices are adjacent, each helper $(i,j;m)$ is adjacent exactly to the three main vertices $i$, $j$ and $m$, and no two helpers are adjacent. Write $N_{T_t}(u)$ for the set of neighbours of a vertex $u$ in $T_t$.
--
--   **Theorem.** If $t\ge2$, then every vertex of the template graph has at least one neighbour:
--   $$
--   N_{T_t}(u)\neq\emptyset\qquad\text{for every } u\in[t]\sqcup\mathcal{H}_t.
--   $$
--
--   Positive degree is the hypothesis under which the parity-constrained tag sets of the lifts have a uniform size: for a vertex $u$ of degree $\delta\ge1$, the bit assignments $z\colon N_{T_t}(u)\to\mathbb{F}_2$ with a prescribed value of $\sum_{v\in N_{T_t}(u)}z(v)$ are in bijection with arbitrary assignments on the neighbours other than one fixed neighbour, so there are $2^{\delta-1}$ of them whatever the prescribed parity. It is used to show that the zero and star lifts of a base graph over $T_t$ have the same number of vertices, and to bound that number.
--
--   **Formalization Note** The template vertices form the sum type `Fin t ⊕ Helper t`, and the statement is `((template t).neighborSet a).Nonempty`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/TagSizes.lean#L65-L80

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

open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical
variable {I : Type} [Fintype I]

theorem OAI.ParityWL.template_positive_degree {t : ℕ} (ht : 2 ≤ t) (a : TemplateVertex t) :
    ((template t).neighborSet a).Nonempty := by sorry
