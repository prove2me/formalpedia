-- Prove2me | Theorems.Thm_OAI_TalagrandDiscreteConvexity_weightBin_cost_bound
-- name    : OAI.TalagrandDiscreteConvexity.weightBin_cost_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T15:48:50.478707+00:00
-- url     : https://prove2.me/theorems/6ef07f50-6c41-4105-8e5a-fa6448ae04ff
-- title:
--   Every weight bin satisfies the size hypothesis of the covering lemma
-- statement:
--   Let $X$ be finite and $W\ge0$ a weight on subsets of $X$. The large weights are the nonempty $U$ with $(1/2)^{64|U|}\le W(U)$. The small weights are the nonempty $U$ with $0<W(U)<(1/2)^{64|U|}$; such a $U$ lies in the bin $(|U|,e(W(U)))$, where $e$ is the dyadic exponent, so that $(1/2)^{e+1}<W(U)\le(1/2)^e$. Let $q>0$ and assume the global bound $\sum_{U\subseteq X}q^{|U|}W(U)\le1$. For every bin $(r,h)$ with members $\mathcal{S}_{r,h}$,
--   $$
--   |\mathcal{S}_{r,h}|\Bigl(\frac{q}{2^{70}}\Bigr)^r\le2^{h+1} .
--   $$
--
--   Each bin can therefore be fed into the elementary covering lemma with parameter $h$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/Bins.lean#L81-L98

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

theorem OAI.TalagrandDiscreteConvexity.weightBin_cost_bound {q : ℝ} {W : Finset α → ℝ}
    (hq : 0 < q) (hW : ∀ U, 0 ≤ W U)
    (hglobal : (∑ U : Finset α, q ^ U.card * W U) ≤ 1) (b : ℕ × ℕ) :
    ((weightBin W b).card : ℝ) * (q / (2 : ℝ) ^ 70) ^ b.1 ≤
      (2 : ℝ) ^ (b.2 + 1) := by sorry
