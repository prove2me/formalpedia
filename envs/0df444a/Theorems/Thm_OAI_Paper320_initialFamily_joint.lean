-- Prove2me | Theorems.Thm_OAI_Paper320_initialFamily_joint
-- name    : OAI.Paper320.initialFamily_joint
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:55:31.946976+00:00
-- url     : https://prove2.me/theorems/1f2be1ef-695e-4c28-a6ef-0f369a1bf52d
-- title:
--   The initial Hamming-ball family has joint sensitivity zero
-- statement:
--   Fix $d, M \in \mathbb{N}$, write $[n] = \{0, \dots, n-1\}$, identify Boolean values with $\{0,1\}$, and consider the coordinate grid $[M] \times [d+2]$ with Hamming distance $d_H$. For $j \in [M]$ let $z_j$ be the indicator vector of row $j$ (equal to $1$ exactly at the coordinates $(j, \ell)$). The initial family consists of the $d+1$ predicates
--   $$
--   G_q(x) = 1 \iff \exists\, j \in [M]:\ d_H(x, z_j) \le d - q, \qquad q = 0, 1, \dots, d .
--   $$
--   For Boolean functions $g, g'$ and an input $x$, let $s(g, g'; x)$ be the number of coordinates whose flip changes both $g(x)$ and $g'(x)$. For $b \in \{0,1\}$, the joint sensitivity profile $J_b(G)$ is the maximum of $s(G_q, G_{q'}; x)$ over all $0 \le q < q' \le d$ and all inputs $x$ with $G_q(x) = G_{q'}(x) = b$, and $0$ if there are no such triples.
--
--   Then, for both values of $b$,
--   $$
--   J_0(G) = J_1(G) = 0 .
--   $$
--   Equivalently, whenever $q < q'$ and $G_q$, $G_{q'}$ take the same value at $x$, no single coordinate flip changes both $G_q(x)$ and $G_{q'}(x)$.
--
--   These are the initial values of the joint profiles in the recursive construction separating block sensitivity from sensitivity, where they enter the linear recurrences that bound the sensitivity of the terminal predicate.
--
--   **Formalization Note** The statement is `jointSensitivity (initialFamily d M) b = 0` for all `d M : ℕ` and `b : Bool`. No assumption on $d$ or $M$ is needed; for $M = 0$ every $G_q$ is constantly false.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/InitialPredicates.lean#L113-L136

import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates

open OAI OAI.Paper320
open scoped Classical

theorem OAI.Paper320.initialFamily_joint (d M : ℕ) (b : Bool) :
    jointSensitivity (initialFamily d M) b = 0 := by sorry
