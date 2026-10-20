-- Prove2me | Theorems.Thm_OAI_TalagrandThreshold_Selector_feasibleFor_delayColor
-- name    : OAI.TalagrandThreshold.Selector.feasibleFor_delayColor
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T13:00:34.824038+00:00
-- url     : https://prove2.me/theorems/b6bc8666-06ba-47ec-a3b6-11098fc2f598
-- title:
--   Delaying a light moved point preserves feasibility
-- statement:
--   Fix $s\in\mathbb{N}$. Colors are $0,\dots,s$ and a coloring of a finite set $X$ is a map $a:X\to\{0,\dots,s\}$. For $i<s$, $P_i(z)=\{x:z(x)\le i\}$, $d_i=2^{-(i+1)}$, the crossings are $|P_i(z)\setminus P_i(a)|$, the moved row $i$ is $\{x:z(x)=i<a(x)\}$, and the movement is $\sum_x(a(x)-z(x))$. The profile $n_{a,z}(i,h)$ counts points with final color $i$ and original color $h>i$. For $w:X\to\mathbb{R}$, $A\subseteq X$ and $d,u\in\mathbb{R}$, the truncated excess is $E_A(d,u)=\sum_x\min(w(x),u)([x\in A]-(1-d))$. A cutoff $u$ is admissible for $(w,A,m,d)$ if $0\le u\le1$, every $x$ with $w(x)>u$ lies in $A$, and $mu\le E_A(d,u)$. The heavy set at $u$ is $\{x:w(x)>u\}$. Delaying $x$ at $i$ replaces $z(x)$ by $i+1$. A mass family gives each member $H$ a probability vector $\mu_H$, and $z$ is feasible for $(a,H)$ if each scale $i<s$ has a cutoff admissible for $(\mu_H,P_i(z),\text{crossings}_i(a,z),d_i)$.
--
--   Let $z$ be feasible for $(a,H)$, let $z(x)=i<a(x)$, and let $\varepsilon$ be admissible at scale $i$ with $\mu_H(x)\le\varepsilon$. Then
--   $$
--   \text{the delay of }z\text{ at }x\text{ is feasible for }(a,H).
--   $$
--
--   So a selected move cannot contain a light moved point: the delay would be feasible with smaller movement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/SelectorDelayFeasibility.lean#L64-L91

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

theorem OAI.TalagrandThreshold.Selector.feasibleFor_delayColor {F : Family α} (mu : MassFamily F) {s : ℕ}
    (a z : Coloring α s) (H : ↥F) (hfeasible : FeasibleFor mu a z H)
    (x : α) (i : Fin s) (hx : (z x).val = i.val)
    (hmove : (z x).val < (a x).val) (ε : ℝ)
    (hε : Admissible (mu.weight H) (prefixSet z i)
      (crossings a z i : ℝ) (dscale i) ε)
    (hweight : mu.weight H x ≤ ε) :
    FeasibleFor mu a (delayColor z x i) H := by sorry
