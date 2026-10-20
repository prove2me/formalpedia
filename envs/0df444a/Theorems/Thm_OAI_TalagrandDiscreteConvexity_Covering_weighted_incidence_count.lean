-- Prove2me | Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_weighted_incidence_count
-- name    : OAI.TalagrandDiscreteConvexity.Covering.weighted_incidence_count
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T15:51:52.258992+00:00
-- url     : https://prove2.me/theorems/66e4e85b-5165-481a-aeb5-efae53f9e129
-- title:
--   Weighted incidence identity for weighted degrees
-- statement:
--   Let $V$ be finite, $H$ a family of $r$-element subsets of $V$, and $\rho\in\mathbb{R}$. With $d(I)=\#\{e\in H:I\subseteq e\}\rho^{r-|I|}$,
--   $$
--   \sum_{|I|\le r}d(I)\,\rho^{|I|}=2^r|H|\rho^r .
--   $$
--
--   The identity holds even for $\rho=0$. It says the weighted degrees have a fixed total budget.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/CoveringRegularization.lean#L56-L78

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

theorem OAI.TalagrandDiscreteConvexity.Covering.weighted_incidence_count (H : Family V) (rho : ℝ) (r : ℕ)
    (hH : ∀ e ∈ H, e.card = r) :
    (∑ I ∈ Finset.univ.filter (fun I : Finset V => I.card ≤ r),
      weightedDegree H rho r I * rho ^ I.card) =
      (2 : ℝ) ^ r * (H.card : ℝ) * rho ^ r := by sorry
