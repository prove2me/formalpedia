-- Prove2me | Theorems.Thm_OAI_TalagrandThreshold_card_rowEncoding
-- name    : OAI.TalagrandThreshold.card_rowEncoding
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:54:55.211654+00:00
-- url     : https://prove2.me/theorems/7226b401-c752-4671-bec7-3fad0c751141
-- title:
--   Counting row encodings
-- statement:
--   Let $X$ and $H$ be finite, $R\subseteq X$, $t\in\mathbb{N}$ and $n:H\to\mathbb{N}$. The row encodings are the pairs $(U,f)$ with $U\subseteq R$, $|U|=t$ and $f:U\to H$ of profile $n$. Their number is
--   $$
--   \binom{|R|}{t}\,W_t(n),
--   $$
--   where $W_t(n)$ is the number of words of length $t$ with profile $n$.
--
--   Every $t$-element subset carries the same number of words of a given profile. The count therefore factors.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/SelectorCountingEncodingRows.lean#L42-L62

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

open OAI OAI.TalagrandThreshold
open scoped BigOperators
variable {α H : Type*} [Fintype α] [DecidableEq α] [Fintype H] [DecidableEq H]

theorem OAI.TalagrandThreshold.card_rowEncoding (R : Finset α) (t : ℕ) (n : H → ℕ) :
    Fintype.card (RowEncoding R t n) = Nat.choose R.card t * wordCount t n := by sorry
