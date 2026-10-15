-- Prove2me | Theorems.Thm_OAI_Paper320_recursive_joint_one_at
-- name    : OAI.Paper320.recursive_joint_one_at
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:56:57.764764+00:00
-- url     : https://prove2.me/theorems/f13dc882-f083-4318-8abb-f7382505723c
-- title:
--   Joint sensitivity of two next-level row-clause predicates at a common accepted input
-- statement:
--   Fix a tournament $T$ on $[k] = \{0, \dots, k-1\}$, with edge relation $i \to j$, in which every vertex has exactly $o$ out-neighbours; a labeling $\lambda : [k] \times [k] \to [r]$; a finite set $I$; and a family $F = (F_0, \dots, F_h)$ of $h+1$ Boolean functions on $\{0,1\}^I$, Boolean values being identified with $\{0,1\}$. The next level of the row-clause construction lives on the coordinate set $([k] \times [r]) \times I$; an input $x$ there has children $x[j,c] \in \{0,1\}^I$ given by $x[j,c](a) = x((j,c),a)$. For $q \in \{0, \dots, h-1\}$ the gate index is $h-1-q$, the row clauses are
--   $$
--   C_{q,i}(x) = 1 \iff \Big( \forall\, c \in [r]:\ F_h(x[i,c]) = 1 \Big) \text{ and } \Big( \forall\, j \text{ with } i \to j:\ F_{h-1-q}\big(x[j,\lambda(i,j)]\big) = 0 \Big),
--   $$
--   and the next-level predicates are $F'_q = \bigvee_{i \in [k]} C_{q,i}$.
--
--   Assume moreover that $F$ is nested: for all indices $p \le p'$ and all inputs $y$, $F_{p'}(y) = 1$ implies $F_p(y) = 1$. Write $s(g,y)$ for the sensitivity of a Boolean function $g$ at $y$, and $s(g, g'; y)$ for the joint sensitivity of $g$ and $g'$ at $y$, the number of coordinates whose flip changes both $g(y)$ and $g'(y)$. Let $S_1(F)$ be the maximum of $s(F_p, y)$ over all indices $p$ and all inputs $y$ with $F_p(y) = 1$, and let $J_0(F)$ be the maximum of $s(F_p, F_{p'}; y)$ over all indices $p < p'$ and all inputs $y$ with $F_p(y) = F_{p'}(y) = 0$ (each maximum being $0$ over an empty range).
--
--   Then for all $0 \le q < q' \le h-1$ and every input $x$ with $F'_q(x) = F'_{q'}(x) = 1$,
--   $$
--   s(F'_q, F'_{q'}; x) \le o \cdot J_0(F) + r \cdot S_1(F) .
--   $$
--
--   Taking the maximum over $q < q'$ and over common accepted inputs gives the recurrence $J_1(F') \le o\, J_0(F) + r\, S_1(F)$ for the joint profile of the next level on accepted inputs, one of the linear recurrences that control the sensitivity in the construction separating block sensitivity from sensitivity.
--
--   **Formalization Note** The predicates are `recursiveFamily T label F q`; the quantities are `jointSensitivityAt`, `sideSensitivity F true` and `jointSensitivity F false` (maxima as `Finset.sup`); nestedness is `NestedFamily F`; and the out-degree hypothesis is `∀ i, (Finset.univ.filter (T.Adj i)).card = o`. The gate index $h-1-q$ is `gateIndex q`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/RecursiveOne.lean#L72-L135

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

open OAI OAI.Paper320
open scoped Classical

theorem OAI.Paper320.recursive_joint_one_at {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (o : ℕ)
    (ho : ∀ i, (Finset.univ.filter (T.Adj i)).card = o)
    (q q' : Fin h) (hqq : q < q') (x : ((Fin k × Fin r) × I) → Bool)
    (hx : recursiveFamily T label F q x = true)
    (hx' : recursiveFamily T label F q' x = true) :
    jointSensitivityAt (recursiveFamily T label F q) (recursiveFamily T label F q') x ≤
      o * jointSensitivity F false + r * sideSensitivity F true := by sorry
