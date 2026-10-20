-- Prove2me | Theorems.Thm_OAI_TalagrandDiscreteConvexity_largeWeightFamily_cost_le
-- name    : OAI.TalagrandDiscreteConvexity.largeWeightFamily_cost_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T15:49:20.94409+00:00
-- url     : https://prove2.me/theorems/4d47d36b-cae0-41c9-8cdb-7598b44a052a
-- title:
--   All large weights together cost at most $1/64$
-- statement:
--   Let $X$ be finite and $W\ge0$ a weight on subsets of $X$. The large weights are the nonempty $U$ with $(1/2)^{64|U|}\le W(U)$. The small weights are the nonempty $U$ with $0<W(U)<(1/2)^{64|U|}$; such a $U$ lies in the bin $(|U|,e(W(U)))$, where $e$ is the dyadic exponent, so that $(1/2)^{e+1}<W(U)\le(1/2)^e$. For a family $\mathcal{G}$ of finite sets and $\rho\in\mathbb{R}$, the cost is $\mathrm{cost}_\rho(\mathcal{G})=\sum_{I\in\mathcal{G}}\rho^{|I|}$, and $\mathcal{G}$ covers $\mathcal{A}$ if every member of $\mathcal{A}$ contains a member of $\mathcal{G}$. Let $q\ge0$ and $\sum_Uq^{|U|}W(U)\le1$. Then the large weights, used as generators, satisfy
--   $$
--   \mathrm{cost}_{q/2^{70}}(\text{large weights})\le\frac1{64}.
--   $$
--
--   Sets of large weight are covered directly. The small weights are handled bin by bin.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/Bins.lean#L100-L116

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

theorem OAI.TalagrandDiscreteConvexity.largeWeightFamily_cost_le {q : ℝ} {W : Finset α → ℝ}
    (hq : 0 ≤ q) (hW : ∀ U, 0 ≤ W U)
    (hglobal : (∑ U : Finset α, q ^ U.card * W U) ≤ 1) :
    cost (q / (2 : ℝ) ^ 70) (largeWeightFamily W) ≤ 1 / 64 := by sorry
