-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_FiniteEntropy_relTerm_nonneg
-- name    : OAI.CliqueFreeIndependence.FiniteEntropy.relTerm_nonneg
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T21:24:06.316321+00:00
-- url     : https://prove2.me/theorems/915d0ff6-774f-492b-abff-8718167aaed6
-- title:
--   Nonnegativity of the relative-entropy term $p\log(p/q)-p+q$
-- statement:
--   Let $p$ and $q$ be real numbers with $p\ge0$ and $q\ge0$, and assume that $q>0$ whenever $p>0$. Then
--
--   $$
--   p\log\frac pq-p+q\ge0,
--   $$
--
--   where $\log$ is the natural logarithm and, for $p=0$, the term $p\log(p/q)$ is read as $0$ (so the expression equals $q$).
--
--   This is the pointwise inequality behind the nonnegativity of the generalized Kullback–Leibler divergence $\sum_i\bigl(p_i\log(p_i/q_i)-p_i+q_i\bigr)$ between nonnegative vectors; it is the inequality $\log y\le y-1$ in another form. It is used repeatedly in entropy estimates and in monotonicity arguments for functions of the form $s\log(1/s)$.
--
--   **Formalization Note** In Lean $0\cdot\log(0/q)=0$ automatically. The support hypothesis excludes the case $p>0$, $q=0$, where Lean's conventions ($p/0=0$ and $\log 0=0$) would turn the expression into $-p<0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/FiniteEntropy.lean#L32-L45

import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.FiniteEntropy
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v
variable {I : Type u} [Fintype I]

theorem OAI.CliqueFreeIndependence.FiniteEntropy.relTerm_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hs : 0 < p → 0 < q) : 0 ≤ p * Real.log (p / q) - p + q := by sorry
