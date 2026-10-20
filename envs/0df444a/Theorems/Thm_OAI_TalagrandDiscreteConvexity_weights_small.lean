-- Prove2me | Theorems.Thm_OAI_TalagrandDiscreteConvexity_weights_small
-- name    : OAI.TalagrandDiscreteConvexity.weights_small
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:10:08.791831+00:00
-- url     : https://prove2.me/theorems/c3ad6190-931b-4418-8277-b5a5736967a2
-- title:
--   Weights with a global budget and a lower bound on a family make it small
-- statement:
--   For a family $\mathcal{G}$ of finite sets and $\rho\in\mathbb{R}$, $\mathrm{cost}_\rho(\mathcal{G})=\sum_{I\in\mathcal{G}}\rho^{|I|}$; $\mathcal{G}$ covers $\mathcal{A}$ if every member of $\mathcal{A}$ contains a member of $\mathcal{G}$, and $\mathcal{A}$ is $\rho$-small if it has a cover of cost at most $\frac12$.
--
--   Let $X$ be finite, $0<q<1$, $\mathcal{A}$ a family of subsets of $X$, and $W\ge0$ a weight on subsets of $X$. Assume
--   $$
--   \sum_{U\subseteq X}q^{|U|}W(U)\le1\qquad\text{and}\qquad\sum_{\emptyset\ne U\subseteq S}W(U)^{16}\ge2^{-32}\ \text{ for every }S\in\mathcal{A}.
--   $$
--   Then $\mathcal{A}$ is $q/2^{70}$-small.
--
--   The weights act as a fractional certificate. A global budget at density $q$ and a local lower bound on each target set produce an actual cover at a slightly smaller density.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/WeightedCover.lean#L21-L90

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

open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem OAI.TalagrandDiscreteConvexity.weights_small {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (A : Family α) (W : Finset α → ℝ) (hW : ∀ U, 0 ≤ W U)
    (hglobal : (∑ U : Finset α, q ^ U.card * W U) ≤ 1)
    (hlower : ∀ S ∈ A,
      (1 / 2 : ℝ) ^ 32 ≤ ∑ U ∈ S.powerset.erase ∅, (W U) ^ 16) :
    Small (q / (2 : ℝ) ^ 70) A := by sorry
