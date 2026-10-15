-- Prove2me | Theorems.Thm_OAI_Paper320_Tournament_card_badLabelings_le
-- name    : OAI.Paper320.Tournament.card_badLabelings_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:52:48.094585+00:00
-- url     : https://prove2.me/theorems/6e4766bf-d1d1-4426-970d-ba9363ed182f
-- title:
--   Union bound for labelings that are target-constant on some $n$-vertex set
-- statement:
--   Let $T$ be a tournament on $[k] = \{0, \dots, k-1\}$ with edge relation $i \to j$, and let $n \ge 1$ and $r$ be natural numbers. A labeling is any map $A : [k] \times [k] \to [r]$; there are $r^{k^2}$ of them. For a map $v : [n] \to [k]$ and target labels $m : [n] \to [r]$, define the event
--   $$\mathcal{E}(v,m) = \begin{cases} \{ A : A(v(i), v(j)) = m(j) \text{ for all } i, j \in [n] \text{ with } v(i) \to v(j) \}, & v \text{ injective},\\ \emptyset, & \text{otherwise,} \end{cases}$$
--   and call a labeling bad if it lies in some event: $\mathrm{Bad}_n = \bigcup_{v} \bigcup_{m} \mathcal{E}(v,m)$. Thus $A$ is bad when some set of $n$ vertices admits target labels such that every edge inside the set carries the target label of its head. Then
--
--   $$
--   |\mathrm{Bad}_n| \le k^n \, r^n \, r^{\,k^2 - \binom{n}{2}} .
--   $$
--
--   With $n = 16$ this is the union bound behind the existence of good labelings: whenever $k^{16} r^{16} r^{k^2 - 120} < r^{k^2}$, some labeling is not bad, and such a labeling has no target-constant set of $16$ vertices.
--
--   **Formalization Note** The hypothesis $n \ge 1$ is the instance `[NeZero n]`. The exponent `k*k - n.choose 2` uses truncated natural-number subtraction; truncation is harmless, since $\binom{n}{2} > k^2$ forces $n > k$, in which case no injective $v$ exists and $\mathrm{Bad}_n$ is empty. The bad set is `T.badLabelings n r` and the events are `T.labelingEvent v m`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/LabelingEvents.lean#L65-L77

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
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveFailures
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveCandidates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tower
import Definitions.Def_OAI_Combinatorics_Sensitivity_TowerProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_ProfileArithmetic
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_OAI_Combinatorics_Sensitivity_Or
import Definitions.Def_OAI_Combinatorics_Sensitivity_Reindex
import Definitions.Def_OAI_Combinatorics_Sensitivity_Construction
import Definitions.Def_OAI_Combinatorics_Sensitivity_FixedCoordinates
import Definitions.Def_OAI_Combinatorics_Sensitivity_LabelingEvents

open OAI OAI.Paper320 OAI.Paper320.Tournament
open scoped Classical BigOperators
variable {k r n : ℕ} (T : Tournament k)

theorem OAI.Paper320.Tournament.card_badLabelings_le [NeZero n] :
    (T.badLabelings n r).card ≤ k^n * r^n * r^(k*k-n.choose 2) := by sorry
