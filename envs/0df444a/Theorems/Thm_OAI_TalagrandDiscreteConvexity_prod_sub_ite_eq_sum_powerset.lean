-- Prove2me | Theorems.Thm_OAI_TalagrandDiscreteConvexity_prod_sub_ite_eq_sum_powerset
-- name    : OAI.TalagrandDiscreteConvexity.prod_sub_ite_eq_sum_powerset
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:12:08.235983+00:00
-- url     : https://prove2.me/theorems/485c9411-d715-4438-9b0d-e9201264ed42
-- title:
--   Expanding a product with corrections on a subset
-- statement:
--   Let $V$ be finite, $S\subseteq V$ and $P,C:V\to\mathbb{R}$. Then
--   $$
--   \prod_{i\in V}\bigl(P_i-[i\in S]\,C_i\bigr)=\sum_{U\subseteq S}(-1)^{|U|}\prod_{i\in V}\begin{cases}C_i,&i\in U,\\P_i,&i\notin U.\end{cases}
--   $$
--
--   Expanding the product of the column factors of a signed array produces a signed sum over subsets $U\subseteq S$, one row kernel for each $U$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/ColumnExpansion.lean#L37-L62

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
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringSampledFamilies
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteProbability
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bernoulli
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringResidualTuples
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringNumericalBounds
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FourierWeights

open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem OAI.TalagrandDiscreteConvexity.prod_sub_ite_eq_sum_powerset (S : Finset V) (P C : V → ℝ) :
    (∏ i, (P i - if i ∈ S then C i else 0)) =
      ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * ∏ i, if i ∈ U then C i else P i := by sorry
