-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_deficitPotential_step
-- name    : OAI.SeymourSecondNeighborhood.deficitPotential_step
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T12:06:18.098182+00:00
-- url     : https://prove2.me/theorems/c9ec3f2f-a160-45ae-be49-e2d21b04b58f
-- title:
--   In an arc-minimal counterexample the deficit potential gains strictly less than the added boundary
-- statement:
--   Let $V$ be a finite set and $r$ a relation on $V$, viewed as a digraph with arcs $x\to y$. It is oriented if it has no loops and no 2-cycles. $N^+(v)$ is the out-neighbourhood, and $N^{++}(v)$ is the set of $w\ne v$, $w\notin N^+(v)$, reachable by a path $v\to u\to w$. A counterexample is an oriented digraph with $|N^{++}(v)|<|N^+(v)|$ for every $v$. For $S\subseteq V$, $r(S)$ is the set of out-neighbours of elements of $S$. Let $r$ be an arc-minimal oriented counterexample. For $S\subseteq V$, let $\partial S=r(S)\setminus S$, and let
--   $$
--   \Phi_S(T)=\Bigl|\,r(T)\setminus\bigl((r(S)\cap S)\cup T\bigr)\Bigr| .
--   $$
--   If $T\subsetneq\partial S$, then there is a nonempty $Q\subseteq\partial S\setminus T$ with
--   $$
--   \Phi_S(T\cup Q)<\Phi_S(T)+|Q| .
--   $$
--
--   This is the augmentation step behind the subset deficit property. It is extracted from arc-minimality by deleting arcs from $S$ to the part of the boundary not yet absorbed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/Deletion.lean#L75-L255

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

theorem OAI.SeymourSecondNeighborhood.deficitPotential_step (r : V → V → Prop) (hr : IsOriented r)
    (hcounter : Counterexample r) (hminimal : ArcMinimal r)
    (S T : Finset V) (hT : T ⊆ image r S \ S)
    (hproper : T ≠ image r S \ S) :
    ∃ Q : Finset V, Q.Nonempty ∧ Q ⊆ (image r S \ S) \ T ∧
      deficitPotential r S (T ∪ Q) < deficitPotential r S T + Q.card := by sorry
