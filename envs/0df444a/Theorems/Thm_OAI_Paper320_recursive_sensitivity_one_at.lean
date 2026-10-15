-- Prove2me | Theorems.Thm_OAI_Paper320_recursive_sensitivity_one_at
-- name    : OAI.Paper320.recursive_sensitivity_one_at
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:56:26.156913+00:00
-- url     : https://prove2.me/theorems/2f3d5cdc-a658-44ef-8c1c-31eec66d18bf
-- title:
--   Sensitivity of a next-level row-clause predicate at an accepted input
-- statement:
--   Fix a tournament $T$ on $[k] = \{0, \dots, k-1\}$, with edge relation $i \to j$, in which every vertex has exactly $o$ out-neighbours; a labeling $\lambda : [k] \times [k] \to [r]$; a finite set $I$; and a family $F = (F_0, \dots, F_h)$ of $h+1$ Boolean functions on $\{0,1\}^I$, Boolean values being identified with $\{0,1\}$. The next level of the row-clause construction lives on the coordinate set $([k] \times [r]) \times I$; an input $x$ there has children $x[j,c] \in \{0,1\}^I$ given by $x[j,c](a) = x((j,c),a)$. For $q \in \{0, \dots, h-1\}$ the gate index is $h-1-q$, the row clauses are
--   $$
--   C_{q,i}(x) = 1 \iff \Big( \forall\, c \in [r]:\ F_h(x[i,c]) = 1 \Big) \text{ and } \Big( \forall\, j \text{ with } i \to j:\ F_{h-1-q}\big(x[j,\lambda(i,j)]\big) = 0 \Big),
--   $$
--   and the next-level predicates are $F'_q = \bigvee_{i \in [k]} C_{q,i}$.
--
--   Write $s(g,y)$ for the sensitivity of a Boolean function $g$ at $y$, the number of coordinates whose flip changes $g(y)$. For $b \in \{0,1\}$ let $S_b(F)$ be the side sensitivity of $F$: the maximum of $s(F_p, y)$ over all indices $p \in \{0, \dots, h\}$ and all inputs $y$ with $F_p(y) = b$ (and $0$ if there are none).
--
--   Then for every $q \in \{0, \dots, h-1\}$ and every input $x$ with $F'_q(x) = 1$,
--   $$
--   s(F'_q, x) \le o \cdot S_0(F) + r \cdot S_1(F) .
--   $$
--
--   Taking the maximum over $q$ and over accepted inputs gives the recurrence $S_1(F') \le o\, S_0(F) + r\, S_1(F)$ for the side sensitivity of the next level on accepted inputs. Neither nestedness of $F$ nor any property of the labeling is needed. For a regular tournament with parameter $M$ one has $o = M^2$.
--
--   **Formalization Note** The predicates are `recursiveFamily T label F q`, the profiles are `sideSensitivity F b` (a `Finset.sup`, hence $0$ over an empty range), and the out-degree hypothesis is `∀ i, (Finset.univ.filter (T.Adj i)).card = o`. The gate index $h-1-q$ is `gateIndex q`, i.e. `(Fin.rev q).castSucc`, and the last index $h$ is `Fin.last h`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/RecursiveOne.lean#L12-L61

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

theorem OAI.Paper320.recursive_sensitivity_one_at {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (o : ℕ)
    (ho : ∀ i, (Finset.univ.filter (T.Adj i)).card = o)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (hx : recursiveFamily T label F q x = true) :
    sensitivityAt (recursiveFamily T label F q) x ≤
      o * sideSensitivity F false + r * sideSensitivity F true := by sorry
