-- Prove2me | Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_regular_extension_le_card
-- name    : OAI.TalagrandDiscreteConvexity.Covering.regular_extension_le_card
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T15:53:02.58199+00:00
-- url     : https://prove2.me/theorems/73c5f4cb-d55c-4c26-95dd-313cdb8757bd
-- title:
--   Extension weight of regular edges over a fixed set
-- statement:
--   Let $H$ be a finite family of $r$-element subsets of $V$ (edges), $\rho\ge0$ and $T\ge0$. The weighted degree of $I\subseteq V$ is $d(I)=\#\{e\in H:I\subseteq e\}\cdot\rho^{r-|I|}$. The initial family consists of the sets $I$ with $|I|\le r$ and $d(I)>T$, and the regular edges are the edges containing no initial set. For every $B\subseteq V$,
--   $$
--   \sum_{e\text{ regular}}\rho^{|e\setminus B|}\le T\cdot\#\{I\subseteq B:\ |I|\le r\} .
--   $$
--
--   This bounds the cost of adding one more regular edge to a union $B$. Iterating it controls the total weight of residual tuples.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/CoveringRegularization.lean#L174-L196

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Definitions.Def_TalagrandDiscreteConvexity
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Model
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Basic
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_DyadicBins
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteFibers
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bins
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringBasic

open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem OAI.TalagrandDiscreteConvexity.Covering.regular_extension_le_card {H : Family V} {rho T : ℝ} {r : ℕ}
    (hρ : 0 ≤ rho) (hT : 0 ≤ T) (hH : ∀ e ∈ H, e.card = r) (B : Finset V) :
    (∑ e ∈ regularEdges H rho r T, rho ^ (e \ B).card) ≤
      T * ((B.powerset.filter (fun I => I.card ≤ r)).card : ℝ) := by sorry
