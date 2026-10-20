-- Prove2me | Theorems.Thm_OAI_TalagrandDiscreteConvexity_original_density_small
-- name    : OAI.TalagrandDiscreteConvexity.original_density_small
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:20:35.817259+00:00
-- url     : https://prove2.me/theorems/9cd10634-fc5b-484b-9f0a-7005a03e9b49
-- title:
--   Talagrand's discrete convexity at the original density
-- statement:
--   Let $X$ be a finite ground set. A family is a finite set of subsets of $X$; $\mu_p(\mathcal{D})=\sum_{S\in\mathcal{D}}p^{|S|}(1-p)^{|X\setminus S|}$ is its $p$-biased measure. $\mathcal{D}^{\cup k}$ is the family of unions of $k$ members of $\mathcal{D}$ (repetitions allowed), and $\mathcal{E}_k(\mathcal{D})$ is the family of sets contained in no such union. A family is $p$-small if some family $\mathcal{G}$ with $\sum_{I\in\mathcal{G}}p^{|I|}\le\frac12$ contains, below every member, one of its sets.
--
--   Let $0<p<1$ and $\mu_p(\mathcal{D})\ge1-2^{-75}$. Then
--   $$
--   \mathcal{E}_{2^{75}}(\mathcal{D})\ \text{is }p\text{-small.}
--   $$
--
--   The sets not covered by any union of $2^{75}$ members of a family of measure nearly $1$ are cheaply covered at the same density. This is a form of Talagrand's discrete convexity statement on any finite ground set.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/Main.lean#L22-L59

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
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_SignedArrays
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_ProductProbability
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_LabelCoupling
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_MandatoryCoupling
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_UnionTuples

open OAI OAI.TalagrandDiscreteConvexity
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem OAI.TalagrandDiscreteConvexity.original_density_small (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (D : Family α) (hD : 1 - 1 / (2 : ℝ) ^ 75 ≤ familyMeasure p D) :
    Small p (exceptional ((2 : ℕ) ^ 75) D) := by sorry
