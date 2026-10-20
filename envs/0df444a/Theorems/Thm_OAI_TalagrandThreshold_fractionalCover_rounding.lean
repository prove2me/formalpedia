-- Prove2me | Theorems.Thm_OAI_TalagrandThreshold_fractionalCover_rounding
-- name    : OAI.TalagrandThreshold.fractionalCover_rounding
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T13:22:13.897689+00:00
-- url     : https://prove2.me/theorems/8d6376d4-0d1f-41dc-8718-ee2358b38e7a
-- title:
--   Rounding a cheap fractional cover to an integral cover
-- statement:
--   Let $X$ be a finite set and $\mathcal{F}$ a family of subsets of $X$. A family $\mathcal{G}$ covers $\mathcal{F}$ if every $H\in\mathcal{F}$ contains some $S\in\mathcal{G}$; its cost at density $p$ is $\sum_{S\in\mathcal{G}}p^{|S|}$, and $\mathcal{F}$ is $p$-small if some cover has cost at most $\frac12$. A fractional cover is a function $g$ on subsets of $X$ with values in $[0,1]$ such that $\sum_{S\subseteq H}g(S)\ge1$ for every $H\in\mathcal{F}$; its cost at density $r$ is $\sum_{S\subseteq X}g(S)r^{|S|}$. Let $0<r\le1$ and let $g$ be a fractional cover of $\mathcal{F}$ of cost at most $\frac12$ at density $r$. Then
--   $$
--   \mathcal{F}\text{ is }\frac{r}{25\cdot512^4}\text{-small}.
--   $$
--
--   This is the rounding step of Talagrand's expectation-threshold comparison with an explicit constant. The support of $g$ may contain subsets of any size.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/RoundingMain.lean#L47-L93

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
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCommonWitness
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_TupleCoefficients
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorGlobalCost
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingMain

open OAI OAI.TalagrandThreshold
open scoped BigOperators
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem OAI.TalagrandThreshold.fractionalCover_rounding (F : Family α) (g : Finset α → ℝ) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hcover : FractionalCover F g)
    (hcost : fracCost r g ≤ 1 / 2) :
    Small (r / ((25 : ℝ) * (512 : ℝ) ^ 4)) F := by sorry
