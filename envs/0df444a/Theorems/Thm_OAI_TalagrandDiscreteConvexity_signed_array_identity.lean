-- Prove2me | Theorems.Thm_OAI_TalagrandDiscreteConvexity_signed_array_identity
-- name    : OAI.TalagrandDiscreteConvexity.signed_array_identity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:13:42.498108+00:00
-- url     : https://prove2.me/theorems/beee35f4-89e6-446e-bb9d-240e35776fac
-- title:
--   Summing signed array masses gives the alternating sum of coefficient powers
-- statement:
--   Let $V$ be finite and $q\in\mathbb{R}$, with $\gamma_q(0)=1-q$, $\gamma_q(1)=-(1-q)$ and bit masses $q$ (for $1$) and $1-q$ (for $0$). For $U\subseteq V$ the row kernel is $K_U(x)=\prod_{i\in U}\gamma_q(x_i)\prod_{i\notin U}\mathrm{mass}_q(x_i)$, and for $f:\{0,1\}^V\to\mathbb{R}$ the coefficient is $b(U)=\sum_xf(x)K_U(x)$. For $k\in\mathbb{N}$ and $S\subseteq V$, the signed mass of an array $X=(X_j)_{j\le k}$ of points of $\{0,1\}^V$ is
--   $$
--   \sigma_S(X)=\prod_{i\in V}\Bigl(\prod_j\mathrm{mass}_q(X_{j,i})-[i\in S]\prod_j\gamma_q(X_{j,i})\Bigr).
--   $$
--   Then
--   $$
--   \sum_{X}\Bigl(\prod_{j}f(X_j)\Bigr)\sigma_S(X)=\sum_{U\subseteq S}(-1)^{|U|}\,b(U)^k .
--   $$
--
--   The identity holds for every real $q$ and every $f$. Combined with the vanishing of the summands on exceptional sets, it gives the alternating identity for the coefficients.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/SignedArrays.lean#L45-L75

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

open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem OAI.TalagrandDiscreteConvexity.signed_array_identity (q : ℝ) (k : ℕ)
    (f : (V → Bool) → ℝ) (S : Finset V) :
    (∑ X : Fin k → V → Bool, (∏ j, f (X j)) * signedArrayMass q S X) =
      ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * b q f U ^ k := by sorry
