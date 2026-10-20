-- Prove2me | Theorems.Thm_OAI_TalagrandDiscreteConvexity_prob_pi_cubeSet_mem_family
-- name    : OAI.TalagrandDiscreteConvexity.prob_pi_cubeSet_mem_family
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:17:47.978679+00:00
-- url     : https://prove2.me/theorems/76bd7297-9d87-4bc5-ad6c-f138dafd7000
-- title:
--   Membership of an observed random set in a family has the biased measure
-- statement:
--   Let $X$ be a finite ground set. A family is a finite set of subsets of $X$; $\mu_p(\mathcal{D})=\sum_{S\in\mathcal{D}}p^{|S|}(1-p)^{|X\setminus S|}$ is its $p$-biased measure. $\mathcal{D}^{\cup k}$ is the family of unions of $k$ members of $\mathcal{D}$ (repetitions allowed), and $\mathcal{E}_k(\mathcal{D})$ is the family of sets contained in no such union. A finite law $\mu$ on a finite set $\Omega$ is a nonnegative weight function summing to $1$, with $\Pr_\mu(P)=\sum_{\omega\in P}\mu(\omega)$ and $\mathbb{E}_\mu f=\sum_\omega\mu(\omega)f(\omega)$. For each $i\in X$ let $\mu_i$ be a finite law on $\Omega_i$ with an observation $\mathrm{obs}_i$ satisfying $\Pr(\mathrm{obs}_i=1)=p$, and let $R=\{i:\mathrm{obs}_i(\omega_i)=1\}$ under the product law. Then for every family $\mathcal{D}$,
--   $$
--   \Pr(R\in\mathcal{D})=\mu_p(\mathcal{D}) .
--   $$
--
--   Each row of the label or mandatory coupling lies in $\mathcal{D}$ with probability exactly $\mu_p(\mathcal{D})$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/CoordinateObservations.lean#L49-L75

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

open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators
variable {α : Type*} [Fintype α] [DecidableEq α]
  {Ω : α → Type*} [∀ i, Fintype (Ω i)]

theorem OAI.TalagrandDiscreteConvexity.prob_pi_cubeSet_mem_family (μ : ∀ i, FiniteLaw (Ω i))
    (obs : ∀ i, Ω i → Bool) (p : ℝ)
    (hobs : ∀ i, (μ i).prob (fun w => obs i w = true) = p) (D : Family α) :
    (FiniteLaw.pi μ).prob (fun ω => cubeSet (fun i => obs i (ω i)) ∈ D) =
      familyMeasure p D := by sorry
