-- Prove2me | Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_NumericalBounds_pair_cost_le
-- name    : OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.pair_cost_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:04:20.106702+00:00
-- url     : https://prove2.me/theorems/10005a46-9e6e-4eeb-9ae5-0b640502f896
-- title:
--   Numerical bound for the expected cost of sampled pairs
-- statement:
--   The covering parameters are $m(h)=2^{12h}$, $T(h)=2^{4h}$, $p(h)=2^{-8h}$ and $A(r,h)=4h+13rh$. For $r\le h$,
--   $$
--   p(h)\,2^{h+1}\,2^r\,T(h)\le2\cdot2^{-2h} .
--   $$
--
--   With the edge-mass hypothesis, the expected cost of the sampled pair unions obeys the same bound as the initial generators.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/CoveringNumericalBounds.lean#L193-L207

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

open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds

theorem OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.pair_cost_le (r h : ℕ) (hrh : r ≤ h) :
    p h * (2 : ℝ) ^ (h + 1) * (2 : ℝ) ^ r * T h ≤
      2 * ((2 : ℝ) ^ (2 * h))⁻¹ := by sorry
