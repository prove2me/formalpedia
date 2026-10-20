-- Prove2me | Theorems.Thm_OAI_TalagrandThreshold_Selector_coloring_eq_of_movedRows
-- name    : OAI.TalagrandThreshold.Selector.coloring_eq_of_movedRows
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:53:30.216595+00:00
-- url     : https://prove2.me/theorems/1e0f8aae-666b-4ed4-8429-f30d5993763e
-- title:
--   An original coloring is determined by its moved rows and their labels
-- statement:
--   Fix $s\in\mathbb{N}$. Colors are $0,\dots,s$ and a coloring is a map $a:X\to\{0,\dots,s\}$. For $i<s$, $P_i(z)=\{x:z(x)\le i\}$ and $d_i=2^{-(i+1)}$. A mass family assigns to every member $H\in\mathcal{F}$ a probability vector $\mu_H$ on $X$ supported in $H$. A cutoff $u$ is admissible for $(w,A,m,d)$ if $0\le u\le1$, every $x$ with $w(x)>u$ lies in $A$, and $mu\le\sum_x\min(w(x),u)([x\in A]-(1-d))$. For colorings $a,z$ and $i<s$, the moved row $i$ is $\{x:z(x)=i<a(x)\}$.
--
--   Let $z$ be earlier than both $a$ and $b$ ($z\le a$ and $z\le b$ pointwise). If $a$ and $b$ have the same moved rows, and $a=b$ on these rows, then
--   $$
--   a=b .
--   $$
--
--   This reconstruction makes the encoding of a profile group by row records injective. It needs no disjointness of the ambient sets containing the rows.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/SelectorCountingEncoding.lean#L19-L43

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

open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
variable {α : Type*} [Fintype α] [DecidableEq α] {s : ℕ}

omit [DecidableEq α] in
theorem OAI.TalagrandThreshold.Selector.coloring_eq_of_movedRows
    {a b z : Coloring α s} (ha : Earlier a z) (hb : Earlier b z)
    (hrows : ∀ i, movedRow a z i = movedRow b z i)
    (hlabels : ∀ i x, x ∈ movedRow a z i → a x = b x) : a = b := by sorry
