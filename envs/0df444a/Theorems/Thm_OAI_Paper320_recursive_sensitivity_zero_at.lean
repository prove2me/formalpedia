-- Prove2me | Theorems.Thm_OAI_Paper320_recursive_sensitivity_zero_at
-- name    : OAI.Paper320.recursive_sensitivity_zero_at
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:02:48.014128+00:00
-- url     : https://prove2.me/theorems/45054b2f-7151-4f6c-ba04-0bd9db947e86
-- title:
--   One row-clause level: sensitivity on rejected inputs is at most $16S_0 + S_1 + 3J_1$
-- statement:
--   Let $T$ be a tournament on $[k] = \{0, \dots, k-1\}$ with edge relation $i \to j$, let $r \ge 1$, and let $\lambda : [k] \times [k] \to [r]$ be a good labeling of $T$: for every set $Q$ of exactly $16$ vertices and every choice of target labels $m : [k] \to [r]$ there is an edge $i \to j$ with $i, j \in Q$ and $\lambda(i,j) \ne m(j)$. Let $I$ be a finite set, identify Boolean values with $\{0,1\}$, and let $F = (F_0, \dots, F_h)$ be a nested family of $h+1$ Boolean functions on $\{0,1\}^I$: whenever $p \le p'$, $F_{p'}(y) = 1$ implies $F_p(y) = 1$.
--
--   For an input $x \in \{0,1\}^{([k] \times [r]) \times I}$, a row $j \in [k]$ and a column $c \in [r]$, the child $x[j,c] \in \{0,1\}^I$ is given by $x[j,c](a) = x((j,c),a)$. One level of the row-clause construction produces the $h$ functions $F'_0, \dots, F'_{h-1}$ on $\{0,1\}^{([k] \times [r]) \times I}$ defined by
--   $$
--   F'_q(x) = 1 \iff \exists\, i \in [k]:\ \big( \forall\, c \in [r]:\ F_h(x[i,c]) = 1 \big) \text{ and } \big( \forall\, j \text{ with } i \to j:\ F_{h-1-q}(x[j, \lambda(i,j)]) = 0 \big).
--   $$
--   The condition for a fixed row $i$ is the row clause $C_{q,i}(x)$; the children $x[i,c]$ are its targets and the children $x[j,\lambda(i,j)]$ its gates.
--
--   For a Boolean function $f$ and an input $y$, the sensitivity $s(f,y)$ is the number of coordinates $a$ with $f(y^{\{a\}}) \ne f(y)$, where $y^{\{a\}}$ is $y$ with coordinate $a$ flipped; for two functions $f, g$, the joint sensitivity $s(f,g;y)$ is the number of coordinates whose flip changes both $f(y)$ and $g(y)$. For $b \in \{0,1\}$ the side and joint sensitivity profiles of $F$ are
--   $$
--   S_b(F) = \max\{ s(F_p, y) : F_p(y) = b \}, \qquad J_b(F) = \max\{ s(F_p, F_{p'}; y) : p < p',\ F_p(y) = F_{p'}(y) = b \},
--   $$
--   where an empty maximum is $0$.
--
--   **Theorem.** For every index $q \in \{0, \dots, h-1\}$ and every input $x$ with $F'_q(x) = 0$,
--   $$
--   s(F'_q, x) \le 16\, S_0(F) + S_1(F) + 3\, J_1(F).
--   $$
--
--   Taking the maximum over $q$ and over the rejected inputs $x$ yields the recurrence $S_0(F') \le 16\, S_0(F) + S_1(F) + 3\, J_1(F)$ for the side sensitivity on rejected inputs, one of the four linear recurrences that govern the sensitivity profiles from one level of the construction to the next. The tournament is arbitrary here; no regularity is assumed.
--
--   **Formalization Note** The labeling is `A.label` for `A : GoodLabeling T r`, the assumption $r \ge 1$ is `0 < r`, and nestedness is `NestedFamily F` for `F : Fin (h + 1) → (I → Bool) → Bool`. The function $F'_q$ is `recursiveFamily T A.label F q`, the gate index $h-1-q$ is `gateIndex q`, and the last index $h$ is `Fin.last h`. The profiles $S_b(F)$ and $J_b(F)$ are `sideSensitivity F b` and `jointSensitivity F b`, with `false` and `true` standing for $0$ and $1$. Since $q$ ranges over `Fin h`, the statement is vacuous when $h = 0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/RecursiveZero.lean#L12-L107

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

open OAI OAI.Paper320
open scoped Classical

theorem OAI.Paper320.recursive_sensitivity_zero_at {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (A : GoodLabeling T r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (hr : 0 < r)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (hx : recursiveFamily T A.label F q x = false) :
    sensitivityAt (recursiveFamily T A.label F q) x ≤
      16 * sideSensitivity F false + sideSensitivity F true + 3 * jointSensitivity F true := by sorry
