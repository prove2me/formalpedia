-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_exists_minimal_counterexample
-- name    : OAI.SeymourSecondNeighborhood.exists_minimal_counterexample
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T12:04:38.098139+00:00
-- url     : https://prove2.me/theorems/29a331c1-e0d4-401e-b576-bfa2986d5ae0
-- title:
--   A counterexample yields an arc-minimal one on $\{0,\dots,n-1\}$ with expansion and positive in-degree
-- statement:
--   Let $V$ be a finite set and $r$ a relation on $V$, viewed as a digraph with arcs $x\to y$. It is oriented if it has no loops and no 2-cycles. $N^+(v)$ is the out-neighbourhood, and $N^{++}(v)$ is the set of $w\ne v$, $w\notin N^+(v)$, reachable by a path $v\to u\to w$. A counterexample is an oriented digraph with $|N^{++}(v)|<|N^+(v)|$ for every $v$. For $S\subseteq V$, $r(S)$ is the set of out-neighbours of elements of $S$. A counterexample $s$ on $\{0,\dots,n-1\}$ is arc-minimal if every counterexample on the same vertex set has at least as many arcs. $s$ has nonempty boundary if $s(S)\setminus S\ne\emptyset$ for every nonempty proper $S$, and positive in-degree if every vertex has an in-neighbour.
--
--   If $V$ is nonempty and $r$ is an oriented counterexample on $V$, then there are $n\ge1$ and a relation $s$ on $\{0,\dots,n-1\}$ such that
--   $$
--   s\ \text{is an oriented counterexample, arc-minimal, with nonempty boundary and positive in-degree.}
--   $$
--
--   This sets up the proof by contradiction: it suffices to rule out counterexamples with these extremal properties.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/MinimalCounterexample.lean#L132-L160

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

open OAI OAI.SeymourSecondNeighborhood
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem OAI.SeymourSecondNeighborhood.exists_minimal_counterexample [Nonempty V] {r : V → V → Prop}
    (hr : IsOriented r) (hbad : Counterexample r) :
    ∃ n : ℕ, 0 < n ∧ ∃ s : Fin n → Fin n → Prop,
      IsOriented s ∧ Counterexample s ∧ ArcMinimal s ∧
        NonemptyBoundary s ∧ PositiveIndegree s := by sorry
