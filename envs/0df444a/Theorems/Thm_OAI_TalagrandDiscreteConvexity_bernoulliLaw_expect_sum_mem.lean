-- Prove2me | Theorems.Thm_OAI_TalagrandDiscreteConvexity_bernoulliLaw_expect_sum_mem
-- name    : OAI.TalagrandDiscreteConvexity.bernoulliLaw_expect_sum_mem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T15:55:41.636996+00:00
-- url     : https://prove2.me/theorems/769eea4b-753e-440b-96c1-77b57d8015e5
-- title:
--   Expected sum over a $p$-random subset
-- statement:
--   Let $X$ be finite, $0\le p\le1$, and $f:X\to\mathbb{R}$. If $W$ is a $p$-random subset of $X$ (each element included independently with probability $p$), then
--   $$
--   \mathbb{E}\Bigl[\sum_{x\in W}f(x)\Bigr]=p\sum_{x\in X}f(x) .
--   $$
--
--   This is linearity of expectation for random subsets. It computes the expected cost of independently sampled generators.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/Bernoulli.lean#L264-L293

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

open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem OAI.TalagrandDiscreteConvexity.bernoulliLaw_expect_sum_mem (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : α → ℝ) :
    (bernoulliLaw p hp0 hp1).expectation (fun W => ∑ x ∈ W, f x) = p * ∑ x, f x := by sorry
