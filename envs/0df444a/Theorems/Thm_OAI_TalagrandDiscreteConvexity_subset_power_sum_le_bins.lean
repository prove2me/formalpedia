-- Prove2me | Theorems.Thm_OAI_TalagrandDiscreteConvexity_subset_power_sum_le_bins
-- name    : OAI.TalagrandDiscreteConvexity.subset_power_sum_le_bins
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T15:49:59.078093+00:00
-- url     : https://prove2.me/theorems/c07de098-b01f-4eda-a7a6-ab3e1dea62a1
-- title:
--   Sixteenth powers of weights inside a set split over the small-weight bins
-- statement:
--   Let $X$ be finite and $W\ge0$ a weight on subsets of $X$. The large weights are the nonempty $U$ with $(1/2)^{64|U|}\le W(U)$. The small weights are the nonempty $U$ with $0<W(U)<(1/2)^{64|U|}$; such a $U$ lies in the bin $(|U|,e(W(U)))$, where $e$ is the dyadic exponent, so that $(1/2)^{e+1}<W(U)\le(1/2)^e$. Let $S\subseteq X$ contain no set of large weight. Then
--   $$
--   \sum_{\emptyset\ne U\subseteq S}W(U)^{16}\le\sum_{b\text{ occupied}}\ \sum_{U\in\mathcal{S}_b,\ U\subseteq S}W(U)^{16} .
--   $$
--
--   Sets not already covered by a large-weight generator have all their weight in the bins. Their lower bound on $\sum W^{16}$ must therefore come from some bin.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/Bins.lean#L134-L163

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

open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem OAI.TalagrandDiscreteConvexity.subset_power_sum_le_bins {W : Finset α → ℝ} (hW : ∀ U, 0 ≤ W U)
    (S : Finset α) (hlarge : ∀ U ∈ largeWeightFamily W, ¬ U ⊆ S) :
    (∑ U ∈ S.powerset.erase ∅, (W U) ^ 16) ≤
      ∑ b ∈ occupiedWeightBins W,
        ∑ U ∈ (weightBin W b).filter (fun U => U ⊆ S), (W U) ^ 16 := by sorry
