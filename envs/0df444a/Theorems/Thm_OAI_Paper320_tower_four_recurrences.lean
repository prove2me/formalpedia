-- Prove2me | Theorems.Thm_OAI_Paper320_tower_four_recurrences
-- name    : OAI.Paper320.tower_four_recurrences
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:06:39.058896+00:00
-- url     : https://prove2.me/theorems/d34dbf4a-9119-44b1-b679-c90364cf7521
-- title:
--   Four linear recurrences for the sensitivity profiles along the tower
-- statement:
--   Let $M \in \mathbb{N}$ and let $T$ be a regular tournament with parameter $M$: a tournament on $[k] = \{0, \dots, k-1\}$ with $k = 2M^2 + 1$ in which every vertex has out-degree exactly $M^2$. Let $r \ge 1$ and let $\lambda : [k] \times [k] \to [r]$ be a good labeling of $T$: for every set $Q$ of exactly $16$ vertices and every $m : [k] \to [r]$ there is an edge $i \to j$ inside $Q$ with $\lambda(i,j) \ne m(j)$. Let $I$ be a finite set, identify Boolean values with $\{0,1\}$, and let $\mathrm{base}$ assign to every $h \in \mathbb{N}$ a family $\mathrm{base}(h)$ of $h$ Boolean functions on $\{0,1\}^I$.
--
--   Write $\mathcal{R}$ for one level of the row-clause construction over $(T, \lambda)$: it turns a family $G = (G_0, \dots, G_h)$ of functions on $\{0,1\}^X$ into the family $\mathcal{R}(G) = (G'_0, \dots, G'_{h-1})$ on $\{0,1\}^{([k] \times [r]) \times X}$, where $G'_q(x) = 1$ if and only if some row $i$ has all children $x[i,c]$, $c \in [r]$, accepted by $G_h$ and every gate child $x[j, \lambda(i,j)]$, $i \to j$, rejected by $G_{h-1-q}$. The tower families are $F^{(0,h)} = \mathrm{base}(h)$ and $F^{(n+1,h)} = \mathcal{R}(F^{(n,h+1)})$. For a family $G$ and $b \in \{0,1\}$, the side profile $S_b(G)$ is the largest sensitivity $s(G_p, y)$ over members and inputs with $G_p(y) = b$, and the joint profile $J_b(G)$ is the largest number of coordinates whose flip changes both $G_p(y)$ and $G_{p'}(y)$, over $p < p'$ and inputs with $G_p(y) = G_{p'}(y) = b$ (empty maxima are $0$).
--
--   Fix $D \in \mathbb{N}$ and define, for a level $n$ and $b \in \{0,1\}$,
--   $$
--   S_n(b) = S_b\big(F^{(n, D-n)}\big), \qquad J_n(b) = J_b\big(F^{(n, D-n)}\big),
--   $$
--   the profiles of the family of $D - n$ functions reached from $\mathrm{base}(D)$ after $n$ levels.
--
--   **Theorem.** Assume that $\mathrm{base}(D)$ is nested, i.e. acceptance by a member with a larger index implies acceptance by every member with a smaller index. Then for every level $n < D$:
--
--   1. $S_{n+1}(1) \le M^2\, S_n(0) + r\, S_n(1)$;
--   2. $J_{n+1}(1) \le M^2\, J_n(0) + r\, S_n(1)$;
--   3. $S_{n+1}(0) \le 16\, S_n(0) + S_n(1) + 3\, J_n(1)$;
--   4. $J_{n+1}(0) \le 16\, S_n(0) + 3\, J_n(1)$.
--
--   The first two recurrences concern accepted inputs and the last two rejected inputs. Together with bounds on the profiles of the initial family and a budget condition relating $\max(r,16)$, $M$ and the number of levels, they control the growth of the side profiles along the tower, roughly like $M^n$ on rejected inputs and $M^{n+1}$ on accepted inputs, which bounds the sensitivity of the final function of the tower.
--
--   **Formalization Note** $S_n(b)$ and $J_n(b)$ are `towerSide T.toTournament A.label base D n b` and `towerJoint T.toTournament A.label base D n b`, with `false` and `true` standing for $0$ and $1$; the good labeling is `A : GoodLabeling T.toTournament r` and $r \ge 1$ is `0 < r`. The count $D - n$ is natural-number subtraction, which is exact here because $n < D$. Only $\mathrm{base}(D)$ is constrained, since all families $F^{(n,D-n)}$ are built from it.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/TowerProfiles.lean#L33-L63

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

open OAI OAI.Paper320
open scoped Classical

theorem OAI.Paper320.tower_four_recurrences {M r : ℕ} {I : Type} [Fintype I]
    (T : RegularTournament M) (A : GoodLabeling T.toTournament r)
    (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (D n : ℕ) (hn : n < D) (hr : 0 < r) (hbase : NestedFamily (base D)) :
    (towerSide T.toTournament A.label base D (n + 1) true ≤
      M ^ 2 * towerSide T.toTournament A.label base D n false +
      r * towerSide T.toTournament A.label base D n true) ∧
    (towerJoint T.toTournament A.label base D (n + 1) true ≤
      M ^ 2 * towerJoint T.toTournament A.label base D n false +
      r * towerSide T.toTournament A.label base D n true) ∧
    (towerSide T.toTournament A.label base D (n + 1) false ≤
      16 * towerSide T.toTournament A.label base D n false +
      towerSide T.toTournament A.label base D n true +
      3 * towerJoint T.toTournament A.label base D n true) ∧
    (towerJoint T.toTournament A.label base D (n + 1) false ≤
      16 * towerSide T.toTournament A.label base D n false +
      3 * towerJoint T.toTournament A.label base D n true) := by sorry
