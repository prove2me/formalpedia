-- Prove2me | Theorems.Thm_OAI_TalagrandThreshold_FiniteLaw_expectation_pi_subset_product
-- name    : OAI.TalagrandThreshold.FiniteLaw.expectation_pi_subset_product
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:47:14.70648+00:00
-- url     : https://prove2.me/theorems/c1274b44-6234-496a-81c5-0ca444e6875f
-- title:
--   Expectation of a product over a subset of independent coordinates
-- statement:
--   Let $(\mu_i)_{i\in I}$ be finite laws on finite sets $A_i$, with product law $\bigotimes_i\mu_i$, let $S\subseteq I$ be finite and $f_i:A_i\to\mathbb{R}$. Then
--   $$
--   \mathbb{E}_{\bigotimes\mu}\Bigl[\prod_{i\in S}f_i(\omega_i)\Bigr]=\prod_{i\in S}\mathbb{E}_{\mu_i}f_i .
--   $$
--
--   Independent coordinates factor every subset product. This gives the expectation of the product score.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/ProbabilitySubsetProduct.lean#L21-L42

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

open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.FiniteLaw
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]
  {A : I → Type*} [∀ i, Fintype (A i)]

theorem OAI.TalagrandThreshold.FiniteLaw.expectation_pi_subset_product (μ : ∀ i, FiniteLaw (A i))
    (S : Finset I) (f : ∀ i, A i → ℝ) :
    (pi μ).expectation (fun ω => ∏ i ∈ S, f i (ω i)) =
      ∏ i ∈ S, (μ i).expectation (f i) := by sorry
