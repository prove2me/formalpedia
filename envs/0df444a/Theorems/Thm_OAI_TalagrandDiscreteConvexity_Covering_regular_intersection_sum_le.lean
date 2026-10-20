-- Prove2me | Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_regular_intersection_sum_le
-- name    : OAI.TalagrandDiscreteConvexity.Covering.regular_intersection_sum_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T15:52:40.853328+00:00
-- url     : https://prove2.me/theorems/b6a30e33-3b56-471d-bacc-76d1e427651d
-- title:
--   Regular edges with a fixed trace on a set have bounded extension weight
-- statement:
--   Let $H$ be a finite family of $r$-element subsets of $V$ (edges), $\rho\ge0$ and $T\ge0$. The weighted degree of $I\subseteq V$ is $d(I)=\#\{e\in H:I\subseteq e\}\cdot\rho^{r-|I|}$. The initial family consists of the sets $I$ with $|I|\le r$ and $d(I)>T$, and the regular edges are the edges containing no initial set. For $B,I\subseteq V$,
--   $$
--   \sum_{\substack{e\text{ regular}\\ e\cap B=I}}\rho^{|e\setminus B|}\le T .
--   $$
--
--   Regular edges avoid all high-degree sets, so few of them can share a given trace. Their extensions outside $B$ carry bounded total weight.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/CoveringRegularization.lean#L130-L172

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

theorem OAI.TalagrandDiscreteConvexity.Covering.regular_intersection_sum_le {H : Family V} {rho T : ℝ} {r : ℕ}
    (hρ : 0 ≤ rho) (hT : 0 ≤ T) (hH : ∀ e ∈ H, e.card = r)
    (B I : Finset V) :
    (∑ e ∈ (regularEdges H rho r T).filter (fun e => e ∩ B = I),
      rho ^ (e \ B).card) ≤ T := by sorry
