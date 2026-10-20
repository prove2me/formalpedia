-- Prove2me | Theorems.Thm_OAI_TalagrandThreshold_Selector_maximal_admissible_card_bound
-- name    : OAI.TalagrandThreshold.Selector.maximal_admissible_card_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T13:06:57.226147+00:00
-- url     : https://prove2.me/theorems/3eb754d9-bfd2-4030-a16e-5388da2b366f
-- title:
--   A maximal admissible cutoff has few heavy points
-- statement:
--   For $w:X\to\mathbb{R}$, $A\subseteq X$ and $d,u\in\mathbb{R}$, the truncated excess is $E_A(d,u)=\sum_x\min(w(x),u)([x\in A]-(1-d))$. A cutoff $u$ is admissible for $(w,A,m,d)$ if $0\le u\le1$, every $x$ with $w(x)>u$ lies in $A$, and $mu\le E_A(d,u)$. The heavy set at $u$ is $\{x:w(x)>u\}$. Let $w\ge0$ with $\sum_xw(x)=1$, $m\ge0$ and $0<d<1$. If $\varepsilon$ is admissible for $(w,A,m,d)$ and no larger cutoff is admissible, then
--   $$
--   d\cdot\#\{x:w(x)>\varepsilon\}\le m .
--   $$
--
--   With $d=d_i=2^{-(i+1)}$ and $m$ the number of crossings, the heavy set at the maximal cutoff has at most $2^{i+1}m$ points. This is the source of the small row supersets in the counting argument.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/SelectorTruncationSlope.lean#L74-L110

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

theorem OAI.TalagrandThreshold.Selector.maximal_admissible_card_bound (w : α → ℝ) (A : Finset α) (m d ε : ℝ)
    (hwnonneg : ∀ x, 0 ≤ w x) (hwsum : ∑ x, w x = 1)
    (hm0 : 0 ≤ m) (_hd0 : 0 < d) (_hd1 : d < 1)
    (hε : Admissible w A m d ε)
    (hmax : ∀ u : ℝ, Admissible w A m d u → u ≤ ε) :
    d * ((heavySet w ε).card : ℝ) ≤ m := by sorry
