-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_blowup_strictSubsetGrowth
-- name    : OAI.SeymourSecondNeighborhood.blowup_strictSubsetGrowth
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:07:55.424653+00:00
-- url     : https://prove2.me/theorems/14127dc2-a8c1-45d0-b013-8cbdc1bcf2d5
-- title:
--   Large blow-ups of a deficit digraph satisfy strict subset growth
-- statement:
--   Let $V$ be a finite set and $r$ a relation on $V$, viewed as a digraph with arcs $x\to y$. It is oriented if it has no loops and no 2-cycles. $N^+(v)$ is the out-neighbourhood, and $N^{++}(v)$ is the set of $w\ne v$, $w\notin N^+(v)$, reachable by a path $v\to u\to w$. A counterexample is an oriented digraph with $|N^{++}(v)|<|N^+(v)|$ for every $v$. For $S\subseteq V$, $r(S)$ is the set of out-neighbours of elements of $S$. For $m\in\mathbb{N}$, let $r^{(m)}$ be the transitive blow-up on $V\times\{0,\dots,m-1\}$. Assume $r$ is oriented, every vertex has an in-neighbour, $r$ has the subset deficit property ($|r(r(S))\setminus r(S)|<|r(S)\setminus S|$ for nonempty proper $S$), and $m>|V|$. Then for every nonempty proper $U\subsetneq V\times\{0,\dots,m-1\}$,
--   $$
--   |U|+\bigl|r^{(m)}(r^{(m)}(U))\bigr|<2\,\bigl|r^{(m)}(U)\bigr| .
--   $$
--
--   Blowing up converts the deficit property, which holds up to rounding, into a clean strict inequality for every vertex set. This is the form used in the final counting contradiction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/TransitiveBlowup.lean#L136-L177

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Tauto
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Basic
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ReductionCore
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Reindex
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MinimalCounterexample
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Deletion
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_TransitiveBlowup

open OAI OAI.SeymourSecondNeighborhood
variable {V : Type*}
variable [Fintype V] [DecidableEq V]

theorem OAI.SeymourSecondNeighborhood.blowup_strictSubsetGrowth {r : V → V → Prop} {m : ℕ}
    (_hr : IsOriented r) (hi : PositiveIndegree r) (hd : SubsetDeficit r)
    (hm : Fintype.card V < m) : StrictSubsetGrowth (blowup r m) := by sorry
