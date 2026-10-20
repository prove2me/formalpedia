-- Prove2me | Theorems.Thm_OAI_TalagrandDiscreteConvexity_weighted_transform_bilinear_expansion
-- name    : OAI.TalagrandDiscreteConvexity.weighted_transform_bilinear_expansion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:10:59.38428+00:00
-- url     : https://prove2.me/theorems/383b78c6-ace3-459e-a985-6f8a9e5fd85f
-- title:
--   Expanding a weighted product of two kernel transforms
-- statement:
--   Let $I,J$ be finite, $K:I\times J\to\mathbb{R}$ a kernel, $r:I\to\mathbb{R}$ weights, and $f,g:J\to\mathbb{R}$. Then
--   $$
--   \sum_{u}r_u\Bigl(\sum_xf(x)K_{u,x}\Bigr)\Bigl(\sum_yg(y)K_{u,y}\Bigr)=\sum_{x,y}f(x)g(y)\sum_ur_uK_{u,x}K_{u,y} .
--   $$
--
--   The weighted pairing of the transforms of $f$ and $g$ is governed by the Gram kernel $\sum_ur_uK_{u,x}K_{u,y}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/FiniteParseval.lean#L22-L44

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
variable {I J : Type*} [Fintype I] [Fintype J]

theorem OAI.TalagrandDiscreteConvexity.weighted_transform_bilinear_expansion
    (K : I → J → ℝ) (r : I → ℝ) (f g : J → ℝ) :
    (∑ u, r u * (∑ x, f x * K u x) * (∑ y, g y * K u y)) =
      ∑ x, ∑ y, f x * g y * (∑ u, r u * K u x * K u y) := by sorry
