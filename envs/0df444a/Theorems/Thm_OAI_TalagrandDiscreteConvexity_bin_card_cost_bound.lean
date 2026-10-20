-- Prove2me | Theorems.Thm_OAI_TalagrandDiscreteConvexity_bin_card_cost_bound
-- name    : OAI.TalagrandDiscreteConvexity.bin_card_cost_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T15:47:49.644747+00:00
-- url     : https://prove2.me/theorems/b49ee87b-a147-455c-b473-0bea233f8ec5
-- title:
--   The lower edge of a bin bounds its size at the reduced density
-- statement:
--   Let $n,r,h\in\mathbb{N}$ and $q>0$ with $n\,q^r(1/2)^{h+1}\le1$. Then
--   $$
--   n\Bigl(\frac{q}{2^{70}}\Bigr)^r\le2^{h+1} .
--   $$
--
--   A bin with $n$ sets of size $r$ and weights above $(1/2)^{h+1}$ has total weight $\ge nq^r(1/2)^{h+1}$, which the global budget bounds by $1$. This is the size hypothesis of the elementary covering lemma at the reduced density.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/BinNumerics.lean#L142-L160

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

theorem OAI.TalagrandDiscreteConvexity.bin_card_cost_bound {n r h : ℕ} {q : ℝ} (hq : 0 < q)
    (hw : (n : ℝ) * q ^ r * (1 / 2 : ℝ) ^ (h + 1) ≤ 1) :
    (n : ℝ) * (q / (2 : ℝ) ^ 70) ^ r ≤ (2 : ℝ) ^ (h + 1) := by sorry
