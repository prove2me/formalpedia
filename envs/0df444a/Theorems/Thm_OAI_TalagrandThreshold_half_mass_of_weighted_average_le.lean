-- Prove2me | Theorems.Thm_OAI_TalagrandThreshold_half_mass_of_weighted_average_le
-- name    : OAI.TalagrandThreshold.half_mass_of_weighted_average_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:48:28.021769+00:00
-- url     : https://prove2.me/theorems/4e061c9d-03f6-4597-8d1f-2b3cae2ebc71
-- title:
--   A weighted Markov inequality
-- statement:
--   Let $T$ be a finite index set and $w,v\ge0$ on $T$ with
--   $$
--   \sum_{i\in T}w_iv_i\le2\sum_{i\in T}w_i .
--   $$
--   Then $\frac12\sum_{i\in T}w_i\le\sum_{i\in T,\ v_i\le4}w_i$.
--
--   If the weighted average of $v$ is at most $2$, at least half of the weight sits where $v\le4$. In the rounding argument, $v$ is the average color of a subset and $w$ its fractional weight.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/RoundingLowerBound.lean#L22-L48

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Definitions.Def_TalagrandExpectationThreshold
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Model
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Basic
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingMasses
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityFinite
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityProduct
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingExpectation

open OAI OAI.TalagrandThreshold
open scoped BigOperators

theorem OAI.TalagrandThreshold.half_mass_of_weighted_average_le {β : Type*} (T : Finset β)
    (w v : β → ℝ) (hw : ∀ i ∈ T, 0 ≤ w i) (hv : ∀ i ∈ T, 0 ≤ v i)
    (hmean : (∑ i ∈ T, w i * v i) ≤ 2 * (∑ i ∈ T, w i)) :
    (∑ i ∈ T, w i) / 2 ≤ ∑ i ∈ T.filter (fun i => v i ≤ 4), w i := by sorry
