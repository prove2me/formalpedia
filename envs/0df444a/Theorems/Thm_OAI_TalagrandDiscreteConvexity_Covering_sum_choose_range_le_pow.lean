-- Prove2me | Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_sum_choose_range_le_pow
-- name    : OAI.TalagrandDiscreteConvexity.Covering.sum_choose_range_le_pow
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T15:50:40.647657+00:00
-- url     : https://prove2.me/theorems/c477681d-f53b-423b-acfd-0b89777cf1a6
-- title:
--   Partial binomial sums are at most $(1+n)^r$
-- statement:
--   For $n,r\in\mathbb{N}$,
--   $$
--   \sum_{i=0}^{r}\binom{n}{i}\le(1+n)^r .
--   $$
--
--   The left side counts subsets of size at most $r$ of an $n$-set. It bounds the number of possible intersections of an $r$-edge with a fixed set.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/CoveringBinomialBounds.lean#L27-L42

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

theorem OAI.TalagrandDiscreteConvexity.Covering.sum_choose_range_le_pow (n r : ℕ) :
    (∑ i ∈ Finset.range (r + 1), Nat.choose n i) ≤ (1 + n) ^ r := by sorry
