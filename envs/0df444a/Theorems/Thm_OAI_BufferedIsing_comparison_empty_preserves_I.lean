-- Prove2me | Theorems.Thm_OAI_BufferedIsing_comparison_empty_preserves_I
-- name    : OAI.BufferedIsing.comparison_empty_preserves_I
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:12:01.393899+00:00
-- url     : https://prove2.me/theorems/bb80a311-c3a3-41f1-b45a-c0a92465683b
-- title:
--   Terminal identifications without open edges preserve membership in the first terminal set
-- statement:
--   Let $G$ be a finite graph on $V=\{0,\dots,n-1\}$ and let $I,J,F\subseteq V$ with $I\cap J=\varnothing$. On the set $V_F=V\setminus F$ of kept vertices, let $\approx$ be the comparison equivalence with no open edges: the smallest equivalence relation on $V_F$ in which any two kept vertices of $I$ are equivalent and any two kept vertices of $J$ are equivalent. Then for all $x,y\in V_F$,
--
--   $$x\approx y\quad\Longrightarrow\quad\bigl(x\in I\iff y\in I\bigr).$$
--
--   Thus contracting $I$ and $J$ separately never merges a vertex of $I$ with a vertex outside $I$; in particular, for $i\in I$ and $j\in J$ the contracted terminals $[i]$ and $[j]$ are distinct vertices of the contracted graph. The edges of $G$ play no role since no edge is open, and no disjointness between $F$ and $I$ or $J$ is assumed.
--
--   **Formalization Note** The relation $\approx$ is `(comparisonSetoid G I J F ∅).r`, the equivalence closure (`Relation.EqvGen`) of `comparisonRel` with the empty edge set. Kept vertices are elements of the subtype `KeptVertex F`, and membership in $I$ is tested on their underlying vertices.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/RandomCluster.lean#L30-L44

import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic

open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem OAI.BufferedIsing.comparison_empty_preserves_I {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (hIJ : Disjoint I J) (x y : KeptVertex F)
    (hxy : (comparisonSetoid G I J F ∅).r x y) :
    x.val ∈ I ↔ y.val ∈ I := by sorry
