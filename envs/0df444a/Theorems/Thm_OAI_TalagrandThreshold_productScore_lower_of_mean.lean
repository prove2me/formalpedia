-- Prove2me | Theorems.Thm_OAI_TalagrandThreshold_productScore_lower_of_mean
-- name    : OAI.TalagrandThreshold.productScore_lower_of_mean
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:49:05.581172+00:00
-- url     : https://prove2.me/theorems/6cd15f82-3754-4b6b-a71e-141188851d30
-- title:
--   A member with small mean color forces a large product score
-- statement:
--   Let $X$ be finite, $g\ge0$ on subsets of $X$, $H\subseteq X$ with $M_g(H)=\sum_{\emptyset\ne S\subseteq H}g(S)\ge\frac12$, and let $\pi_H$ be the rounding mass of $H$. Let $a:X\to\mathbb{N}$ with
--   $$
--   \sum_xa(x)\,\pi_H(x)\le2 .
--   $$
--   Then
--   $$
--   \sum_{\emptyset\ne S\subseteq X}g(S)\prod_{x\in S}\frac{512^4}{512^{a(x)}}\ge\frac14 .
--   $$
--
--   The mean of $a$ under $\pi_H$ is a weighted average of the subset averages of $a$. Subsets with average at most $4$ have product at least $1$, and they carry half the mass.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/RoundingLowerBound.lean#L68-L113

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

theorem OAI.TalagrandThreshold.productScore_lower_of_mean (g : Finset α → ℝ) (H : Finset α)
    (a : α → ℕ) (hg : ∀ S, 0 ≤ g S) (hMH : (1 / 2 : ℝ) ≤ memberMass g H)
    (hmean : (∑ x : α, (a x : ℝ) * roundingMass g H x) ≤ 2) :
    (1 / 4 : ℝ) ≤ productScore g (fun x => (512 : ℝ) ^ 4 / (512 : ℝ) ^ a x) := by sorry
