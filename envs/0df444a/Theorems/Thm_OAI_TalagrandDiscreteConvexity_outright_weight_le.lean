-- Prove2me | Theorems.Thm_OAI_TalagrandDiscreteConvexity_outright_weight_le
-- name    : OAI.TalagrandDiscreteConvexity.outright_weight_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T15:47:26.503809+00:00
-- url     : https://prove2.me/theorems/7ddaf109-c334-4cf3-8ac6-1c1c3de7fb1a
-- title:
--   Large weights pay for their generator at the reduced density
-- statement:
--   Let $r\ge1$, $q\ge0$ and $w\ge(1/2)^{64r}$. Then
--   $$
--   \Bigl(\frac{q}{2^{70}}\Bigr)^r\le\frac1{64}\,q^r\,w .
--   $$
--
--   A set of large weight can be bought outright as a generator. Summed over all large weights, this costs at most $\frac1{64}$ of the global weight budget.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/BinNumerics.lean#L122-L140

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

theorem OAI.TalagrandDiscreteConvexity.outright_weight_le {r : ℕ} {q w : ℝ} (hr : 1 ≤ r) (hq : 0 ≤ q)
    (hw : (1 / 2 : ℝ) ^ (64 * r) ≤ w) :
    (q / (2 : ℝ) ^ 70) ^ r ≤ (1 / 64 : ℝ) * q ^ r * w := by sorry
