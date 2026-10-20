-- Prove2me | Theorems.Thm_OAI_TalagrandDiscreteConvexity_FiniteLaw_expectation_pi_coordinate
-- name    : OAI.TalagrandDiscreteConvexity.FiniteLaw.expectation_pi_coordinate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:14:48.97099+00:00
-- url     : https://prove2.me/theorems/48be636b-3cfd-4601-a1ea-93bb1abfe7b4
-- title:
--   Coordinate marginals of a product law
-- statement:
--   A finite law $\mu$ on a finite set $\Omega$ is a nonnegative weight function summing to $1$, with $\Pr_\mu(P)=\sum_{\omega\in P}\mu(\omega)$ and $\mathbb{E}_\mu f=\sum_\omega\mu(\omega)f(\omega)$. Let $(\mu_i)_{i\in I}$ be finite laws on finite sets $A_i$, and $\bigotimes_i\mu_i$ their product law on $\prod_iA_i$. For every $i$ and $f:A_i\to\mathbb{R}$,
--   $$
--   \mathbb{E}_{\bigotimes\mu}\bigl[f(\omega_i)\bigr]=\mathbb{E}_{\mu_i}f .
--   $$
--
--   Each coordinate of a product law has its prescribed distribution.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/ProductProbability.lean#L34-L55

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

open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.FiniteLaw
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
  {A : I → Type*} [∀ i, Fintype (A i)]

theorem OAI.TalagrandDiscreteConvexity.FiniteLaw.expectation_pi_coordinate (μ : ∀ i, FiniteLaw (A i))
    (i : I) (f : A i → ℝ) :
    (pi μ).expectation (fun ω => f (ω i)) = (μ i).expectation f := by sorry
