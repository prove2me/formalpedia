-- Prove2me | Theorems.Thm_OAI_Paper320_rowClause_repair_cases
-- name    : OAI.Paper320.rowClause_repair_cases
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:02:21.634736+00:00
-- url     : https://prove2.me/theorems/5b1afd4a-d68a-42cd-89d6-db37893533d5
-- title:
--   A single flip that satisfies a failed row clause repairs its only failed condition
-- statement:
--   Use the setting of the row-clause construction: a tournament $T$ on $[k] = \{0, \dots, k-1\}$ with edges $i \to j$, a labeling $\lambda : [k] \times [k] \to [r]$, a set $I$, a family $F = (F_0, \dots, F_h)$ of Boolean functions on $\{0,1\}^I$ (Boolean values identified with $\{0,1\}$), an index $q \in \{0, \dots, h-1\}$ with gate index $g = h - 1 - q$, and inputs $x$ on $([k] \times [r]) \times I$ with children $x[j,c] \in \{0,1\}^I$, $x[j,c](a) = x((j,c),a)$. The row clause $C_{q,i}$ holds at $x$ when $F_h(x[i,c]) = 1$ for all $c \in [r]$ (the targets of row $i$) and $F_g(x[j,\lambda(i,j)]) = 0$ for all $j$ with $i \to j$ (its gates). The target candidates $\mathcal{T}_q(x)$ are the rows with exactly one failed target and no failed gate, and the gate candidates $\mathcal{G}_q(x)$ are the rows with no failed target and exactly one failed gate. For $y \in \{0,1\}^I$ and $a \in I$, $y^{\{a\}}$ is $y$ with coordinate $a$ flipped.
--
--   Let $i, j \in [k]$, $c \in [r]$ and $a \in I$, and let $x^{\{p\}}$ be $x$ with the single coordinate $p = ((j,c),a)$ flipped. If the clause of row $i$ fails at $x$ and holds after the flip,
--   $$
--   C_{q,i}(x) = 0 \qquad \text{and} \qquad C_{q,i}(x^{\{p\}}) = 1,
--   $$
--   then at least one of the following holds:
--
--   1. **Target repair:** $i \in \mathcal{T}_q(x)$, $j = i$, $F_h(x[j,c]) = 0$ and $F_h(x[j,c]^{\{a\}}) = 1$;
--   2. **Gate repair:** $i \in \mathcal{G}_q(x)$, $i \to j$, $c = \lambda(i,j)$, $F_g(x[j,c]) = 1$ and $F_g(x[j,c]^{\{a\}}) = 0$.
--
--   A flip that makes a rejected next-level input accepted must satisfy some row clause, so this result locates every such flip: it acts on the unique failed child of a target-candidate or gate-candidate row. It is the starting point of the recurrences for sensitivity and joint sensitivity on rejected inputs.
--
--   **Formalization Note** No finiteness of $I$ is assumed. The candidate sets are `targetCandidates T label F q x` and `gateCandidates T label F q x`, the gate index is `gateIndex q`, the last index $h$ is `Fin.last h`, and the child $x[j,c]$ is `recursiveChild x j c`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/RecursiveRepair.lean#L35-L97

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

open OAI OAI.Paper320
open scoped Classical

theorem OAI.Paper320.rowClause_repair_cases {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i j : Fin k) (c : Fin r) (a : I)
    (hi : rowClause T label F q x i = false)
    (hf : rowClause T label F q (flip x {((j, c), a)}) i = true) :
    (i ∈ targetCandidates T label F q x ∧ j = i ∧
      F (Fin.last h) (recursiveChild x j c) = false ∧
      F (Fin.last h) (flip (recursiveChild x j c) {a}) = true) ∨
    (i ∈ gateCandidates T label F q x ∧ T.Adj i j ∧ c = label i j ∧
      F (gateIndex q) (recursiveChild x j c) = true ∧
      F (gateIndex q) (flip (recursiveChild x j c) {a}) = false) := by sorry
