-- Prove2me | Theorems.Thm_OAI_TalagrandThreshold_tail_lt_four_mul_p
-- name    : OAI.TalagrandThreshold.tail_lt_four_mul_p
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:50:27.190487+00:00
-- url     : https://prove2.me/theorems/5ef4de0b-1729-4600-bfbb-17a7da91af25
-- title:
--   Failure of the next scale makes the residual color contribution small
-- statement:
--   Let $\Sigma_s=\sum_{i<s}256^{\,i+1}$ and let colors $c\in\{0,\dots,s\}$ have probabilities $256^{c+1}p$ for $c<s$ and $1-p\Sigma_s$ for $c=s$. Let $p>0$ and $s\in\mathbb{N}$ with $p\,\Sigma_{s+1}>\frac12$. Then
--   $$
--   \frac1{512^{\,s+1}}<4p .
--   $$
--
--   The last color has value $512^4/512^{s+1}$ in the rounding score. Choosing $s$ maximal makes its contribution comparable to the other colors.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/ScaleBounds.lean#L121-L135

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
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityColors
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ScaleBounds

open OAI OAI.TalagrandThreshold
open scoped BigOperators

theorem OAI.TalagrandThreshold.tail_lt_four_mul_p {p : ℝ} {s : ℕ} (hp : 0 < p)
    (hnext : 1 / 2 < p * scaleSum (s + 1)) :
    1 / (512 : ℝ) ^ (s + 1) < 4 * p := by sorry
