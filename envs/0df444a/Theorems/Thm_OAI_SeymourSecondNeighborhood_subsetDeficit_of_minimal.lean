-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_subsetDeficit_of_minimal
-- name    : OAI.SeymourSecondNeighborhood.subsetDeficit_of_minimal
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T12:06:51.042149+00:00
-- url     : https://prove2.me/theorems/f9ee9305-025b-42d0-b0a3-8d39f28245c7
-- title:
--   Arc-minimal counterexamples with nonempty boundaries have the subset deficit property
-- statement:
--   Let $V$ be a finite set and $r$ a relation on $V$, viewed as a digraph with arcs $x\to y$. It is oriented if it has no loops and no 2-cycles. $N^+(v)$ is the out-neighbourhood, and $N^{++}(v)$ is the set of $w\ne v$, $w\notin N^+(v)$, reachable by a path $v\to u\to w$. A counterexample is an oriented digraph with $|N^{++}(v)|<|N^+(v)|$ for every $v$. For $S\subseteq V$, $r(S)$ is the set of out-neighbours of elements of $S$. Let $r$ be an oriented counterexample that is arc-minimal and has nonempty boundaries, i.e. $r(S)\setminus S\ne\emptyset$ for every nonempty proper $S$. Then for every nonempty proper $S\subsetneq V$,
--   $$
--   \bigl|r(r(S))\setminus r(S)\bigr|<\bigl|r(S)\setminus S\bigr| .
--   $$
--
--   The second neighbourhood inequality fails not just at single vertices but for all vertex sets. This set version is what makes blow-ups and the extremal pair argument possible.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/SubsetDeficit.lean#L44-L58

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

open OAI OAI.SeymourSecondNeighborhood
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem OAI.SeymourSecondNeighborhood.subsetDeficit_of_minimal {r : V → V → Prop}
    (hr : IsOriented r) (hcounter : Counterexample r)
    (hminimal : ArcMinimal r) (hboundary : NonemptyBoundary r) :
    SubsetDeficit r := by sorry
