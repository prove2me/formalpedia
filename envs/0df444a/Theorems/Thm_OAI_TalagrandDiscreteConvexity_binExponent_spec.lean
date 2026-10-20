-- Prove2me | Theorems.Thm_OAI_TalagrandDiscreteConvexity_binExponent_spec
-- name    : OAI.TalagrandDiscreteConvexity.binExponent_spec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T15:44:41.521017+00:00
-- url     : https://prove2.me/theorems/64c04bbe-bff9-4061-b23f-3b05c4316586
-- title:
--   A weight in $(0,1]$ lies in its dyadic bin
-- statement:
--   Let $0<w\le1$ and let $e(w)$ be its dyadic exponent: one less than the least $m$ with $(1/2)^m<w$. Then
--   $$
--   (1/2)^{e(w)+1}<w\le(1/2)^{e(w)} .
--   $$
--
--   Dyadic bins therefore partition $(0,1]$ into the half-open intervals $((1/2)^{k+1},(1/2)^k]$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/DyadicBins.lean#L26-L43

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

open OAI OAI.TalagrandDiscreteConvexity

theorem OAI.TalagrandDiscreteConvexity.binExponent_spec {w : ℝ} (hwpos : 0 < w) (hwle : w ≤ 1) :
    (1 / 2 : ℝ) ^ (binExponent w + 1) < w ∧
      w ≤ (1 / 2 : ℝ) ^ binExponent w := by sorry
