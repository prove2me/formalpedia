-- Prove2me | Theorems.Thm_OAI_Paper320_Tournament_labelingConstraint_iff
-- name    : OAI.Paper320.Tournament.labelingConstraint_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:50:31.411726+00:00
-- url     : https://prove2.me/theorems/0ec60244-82ad-485e-8c46-f963f2ecf6ef
-- title:
--   Target-constant labeling constraints are prescribed values on internal edges
-- statement:
--   Let $T$ be a tournament on the vertex set $[k] = \{0, \dots, k-1\}$, with edge relation $i \to j$. Let $\alpha$ be a nonempty set, $s \subseteq \alpha$ a finite subset, $v : \alpha \to [k]$ an injective map, $\beta$ any set, $m : \alpha \to \beta$ a map (target values), and $A : [k] \times [k] \to \beta$ a labeling of ordered pairs of vertices. Write
--   $$E_T(v(s)) = \{ (u,w) \in v(s) \times v(s) : u \to w \}$$
--   for the internal edges of the image $v(s)$, and let $v^{-1} : [k] \to \alpha$ be a fixed left inverse of $v$, so $v^{-1}(v(j)) = j$ for all $j$. Then
--
--   $$
--   \Big( \forall\, i, j \in s:\ v(i) \to v(j) \implies A(v(i), v(j)) = m(j) \Big) \iff \Big( \forall\, (u,w) \in E_T(v(s)):\ A(u,w) = m\big(v^{-1}(w)\big) \Big).
--   $$
--
--   The left side says that, on the embedded vertex set, every edge carries the target value of its head; the right side says that $A$ takes prescribed values on the fixed set of internal edges. This reformulation makes the set of labelings satisfying the constraint a set of functions with finitely many fixed coordinates, so it can be counted exactly.
--
--   **Formalization Note** The left inverse is `Function.invFun v`, which requires $\alpha$ to be nonempty (hypothesis `[Nonempty α]`) and is a left inverse because $v$ is injective. The internal edges are `T.internalEdges (s.image v)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/LabelingConstraints.lean#L17-L35

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

open OAI OAI.Paper320 OAI.Paper320.Tournament
open scoped Classical
variable {k : ℕ} (T : Tournament k)

theorem OAI.Paper320.Tournament.labelingConstraint_iff {α β : Type} [Nonempty α]
    (s : Finset α) (v : α → Fin k) (m : α → β) (hv : Function.Injective v)
    (A : (Fin k × Fin k) → β) :
    (∀ i ∈ s, ∀ j ∈ s, T.Adj (v i) (v j) → A (v i,v j) = m j) ↔
      ∀ p ∈ T.internalEdges (s.image v), A p = m (Function.invFun v p.2) := by sorry
