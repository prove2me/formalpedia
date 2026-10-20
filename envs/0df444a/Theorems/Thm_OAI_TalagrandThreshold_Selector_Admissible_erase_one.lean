-- Prove2me | Theorems.Thm_OAI_TalagrandThreshold_Selector_Admissible_erase_one
-- name    : OAI.TalagrandThreshold.Selector.Admissible.erase_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:58:48.056566+00:00
-- url     : https://prove2.me/theorems/dd87d368-4004-4543-80ce-87099c8e8390
-- title:
--   Removing a light point keeps a cutoff admissible with one fewer crossing
-- statement:
--   For $w:X\to\mathbb{R}$, $A\subseteq X$ and $d,u\in\mathbb{R}$, the truncated excess is $E_A(d,u)=\sum_x\min(w(x),u)([x\in A]-(1-d))$. A cutoff $u$ is admissible for $(w,A,m,d)$ if $0\le u\le1$, every $x$ with $w(x)>u$ lies in $A$, and $mu\le E_A(d,u)$. The heavy set at $u$ is $\{x:w(x)>u\}$. Let $u$ be admissible for $(w,A,m,d)$, let $x\in A$ with $w(x)\le u$, and let $m'+1=m$. Then
--   $$
--   u\text{ is admissible for }(w,A\setminus\{x\},m',d).
--   $$
--
--   No maximality of the cutoff is needed. This is the admissibility step behind delaying a light moved point.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/SelectorDelayFeasibility.lean#L45-L62

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
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorTruncationDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorFeasibility
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncoding
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWords
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWordsTransport
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingRows
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorProfile
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingBound
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDelay

open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem OAI.TalagrandThreshold.Selector.Admissible.erase_one {mu : α → ℝ} {A : Finset α} {m m' d u : ℝ}
    (hu : Admissible mu A m d u) {x : α} (hx : x ∈ A)
    (hxu : mu x ≤ u) (hm : m' + 1 = m) :
    Admissible mu (A.erase x) m' d u := by sorry
