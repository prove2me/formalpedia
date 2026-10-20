-- Prove2me | Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_NumericalBounds_residual_cost_le_inv_pow
-- name    : OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.residual_cost_le_inv_pow
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:03:08.253669+00:00
-- url     : https://prove2.me/theorems/edc71b4d-d4f2-44bd-b675-06e4f3ec4203
-- title:
--   The residual tuple factor times its survival probability is at most $2^{-m}$
-- statement:
--   The covering parameters are $m(h)=2^{12h}$, $T(h)=2^{4h}$, $p(h)=2^{-8h}$ and $A(r,h)=4h+13rh$. For $r\le h$ and $h\ge64$,
--   $$
--   \bigl(T(h)(1+r\,m(h))^r\bigr)^{m(h)}\,(1-p(h))^{m(h)^2}\le2^{-m(h)} .
--   $$
--
--   The left side bounds the expected cost of the residual generators. It is negligible next to the cost budget of the covering lemma.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/CoveringNumericalBounds.lean#L152-L168

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

open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds

theorem OAI.TalagrandDiscreteConvexity.Covering.NumericalBounds.residual_cost_le_inv_pow (r h : ℕ) (hrh : r ≤ h) (hh : 64 ≤ h) :
    (T h * (1 + (r : ℝ) * (m h : ℝ)) ^ r) ^ m h *
        (1 - p h) ^ (m h * m h) ≤ ((2 : ℝ) ^ m h)⁻¹ := by sorry
