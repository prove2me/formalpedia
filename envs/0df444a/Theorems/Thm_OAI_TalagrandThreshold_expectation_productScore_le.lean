-- Prove2me | Theorems.Thm_OAI_TalagrandThreshold_expectation_productScore_le
-- name    : OAI.TalagrandThreshold.expectation_productScore_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:48:09.275524+00:00
-- url     : https://prove2.me/theorems/949971f1-8391-4145-a758-e083e7bc9a03
-- title:
--   The expected product score is at most a fifth of the fractional cost
-- statement:
--   Let $X$ be finite, $\nu$ a finite law on $\Omega$, $Y\ge0$ on $\Omega$, $g\ge0$ on subsets of $X$ and $r\ge0$, with $\mathbb{E}_\nu Y\le r/5$. With independent values $\omega_x\sim\nu$,
--   $$
--   \mathbb{E}\Bigl[\sum_{\emptyset\ne S\subseteq X}g(S)\prod_{x\in S}Y(\omega_x)\Bigr]\le\frac15\sum_{S\subseteq X}g(S)r^{|S|} .
--   $$
--
--   Only nonempty sets enter the score. Each of them gains at least one factor $\frac15$, which is where the constant comes from.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/RoundingExpectation.lean#L67-L99

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
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {Ω : Type*} [Fintype Ω]

theorem OAI.TalagrandThreshold.expectation_productScore_le (ν : FiniteLaw Ω) (g : Finset α → ℝ)
    (Y : Ω → ℝ) {r : ℝ} (hg : ∀ S, 0 ≤ g S) (hY : ∀ ω, 0 ≤ Y ω)
    (hr : 0 ≤ r) (hmean : ν.expectation Y ≤ r / 5) :
    (FiniteLaw.pi (fun _ : α => ν)).expectation
        (fun ω => productScore g (fun x => Y (ω x))) ≤
      (1 / 5) * fracCost r g := by sorry
