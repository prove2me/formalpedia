-- Prove2me | Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_expectation_sampledFamily_le
-- name    : OAI.TalagrandDiscreteConvexity.Covering.expectation_sampledFamily_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T15:56:15.930862+00:00
-- url     : https://prove2.me/theorems/3e640920-da23-4c2f-a773-5efd14e7b50d
-- title:
--   Expected cost of the sampled pair unions
-- statement:
--   Let $H$ be a finite family of $r$-element subsets of $V$ (edges), $\rho\ge0$ and $T\ge0$. The weighted degree of $I\subseteq V$ is $d(I)=\#\{e\in H:I\subseteq e\}\cdot\rho^{r-|I|}$. The initial family consists of the sets $I$ with $|I|\le r$ and $d(I)>T$, and the regular edges are the edges containing no initial set. For a family $\mathcal{G}$ of finite sets and $\rho\in\mathbb{R}$, the cost is $\mathrm{cost}_\rho(\mathcal{G})=\sum_{I\in\mathcal{G}}\rho^{|I|}$, and $\mathcal{G}$ covers $\mathcal{A}$ if every member of $\mathcal{A}$ contains a member of $\mathcal{G}$. Sample each ordered pair of regular edges independently with probability $p\in[0,1]$. Then
--   $$
--   \mathbb{E}\bigl[\mathrm{cost}_\rho(\text{sampled pair unions})\bigr]\le p\,|H|\rho^r\,2^rT .
--   $$
--
--   Pairs are sampled as distinct indices even when their unions coincide. Identifying equal unions only lowers the cost.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/CoveringPairCost.lean#L60-L78

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

open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem OAI.TalagrandDiscreteConvexity.Covering.expectation_sampledFamily_le {H : Family V} {rho T p : ℝ} {r : ℕ}
    (hrho : 0 ≤ rho) (hT : 0 ≤ T) (hH : ∀ e ∈ H, e.card = r)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliLaw (α := PairIndex (regularEdges H rho r T)) p hp0 hp1).expectation
        (fun sample => cost rho (sampledFamily (regularEdges H rho r T) sample)) ≤
      p * ((H.card : ℝ) * rho ^ r * (2 : ℝ) ^ r * T) := by sorry
