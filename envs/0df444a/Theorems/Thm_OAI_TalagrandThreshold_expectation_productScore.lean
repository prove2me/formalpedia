-- Prove2me | Theorems.Thm_OAI_TalagrandThreshold_expectation_productScore
-- name    : OAI.TalagrandThreshold.expectation_productScore
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:47:46.252994+00:00
-- url     : https://prove2.me/theorems/306f700e-feb2-485f-bf87-6b012c7e71ef
-- title:
--   Expectation of the product score under independent colors
-- statement:
--   Let $X$ be finite, $\nu$ a finite law on $\Omega$, $Y:\Omega\to\mathbb{R}$, and $g$ a function on subsets of $X$. If the points of $X$ receive independent values $\omega_x\sim\nu$, then
--   $$
--   \mathbb{E}\Bigl[\sum_{\emptyset\ne S\subseteq X}g(S)\prod_{x\in S}Y(\omega_x)\Bigr]=\sum_{\emptyset\ne S\subseteq X}g(S)\,\bigl(\mathbb{E}_\nu Y\bigr)^{|S|} .
--   $$
--
--   The expected product score depends only on the mean of $Y$. When that mean is small, the score is controlled by the fractional cost.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/RoundingExpectation.lean#L36-L53

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

theorem OAI.TalagrandThreshold.expectation_productScore (ν : FiniteLaw Ω) (g : Finset α → ℝ) (Y : Ω → ℝ) :
    (FiniteLaw.pi (fun _ : α => ν)).expectation
        (fun ω => productScore g (fun x => Y (ω x))) =
      ∑ S ∈ (Finset.univ.erase ∅ : Finset (Finset α)),
        g S * (ν.expectation Y) ^ S.card := by sorry
