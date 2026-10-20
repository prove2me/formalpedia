-- Prove2me | Theorems.Thm_OAI_TalagrandDiscreteConvexity_finite_bin_geometric_bound
-- name    : OAI.TalagrandDiscreteConvexity.finite_bin_geometric_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T15:46:06.543215+00:00
-- url     : https://prove2.me/theorems/8311e737-7069-4e02-9ec3-0c972525ac95
-- title:
--   A geometric bound over occupied bins
-- statement:
--   Let $B$ be a finite set of pairs $(r,h)\in\mathbb{N}^2$ with $r\ge1$ and $h\ge64r$, and let $0\le a\le\frac12$. Then
--   $$
--   \sum_{(r,h)\in B}a^h\le4a^{64} .
--   $$
--
--   Each bin of size $r$ and dyadic exponent $h$ contributes at most $a^h$. The bound is uniform over all finite sets of occupied bins.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/BinNumerics.lean#L68-L98

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

open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators

theorem OAI.TalagrandDiscreteConvexity.finite_bin_geometric_bound (B : Finset (ℕ × ℕ))
    (hB : ∀ b ∈ B, 1 ≤ b.1 ∧ 64 * b.1 ≤ b.2) {a : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1 / 2) :
    (∑ b ∈ B, a ^ b.2) ≤ 4 * a ^ 64 := by sorry
