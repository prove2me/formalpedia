-- Prove2me | Theorems.Thm_OAI_TalagrandThreshold_color_mean_le
-- name    : OAI.TalagrandThreshold.color_mean_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:51:13.500339+00:00
-- url     : https://prove2.me/theorems/08628805-39ef-4a63-97d5-d08c27e76d3e
-- title:
--   The mean of the rounding variable under the color law
-- statement:
--   Let $\Sigma_s=\sum_{i<s}256^{\,i+1}$ and let colors $c\in\{0,\dots,s\}$ have probabilities $256^{c+1}p$ for $c<s$ and $1-p\Sigma_s$ for $c=s$. Let $p>0$, $p\Sigma_s\le\frac12$ and $p\Sigma_{s+1}>\frac12$. Then
--   $$
--   \sum_{c=0}^{s}\Pr(c)\,\frac{512^4}{512^{\,c+1}}\le5\cdot512^4\,p .
--   $$
--
--   With $p=r/(25\cdot512^4)$ this is at most $r/5$, which feeds the bound on the expected product score.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/ColorMean.lean#L46-L67

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

open OAI OAI.TalagrandThreshold
open scoped BigOperators

theorem OAI.TalagrandThreshold.color_mean_le {p : ℝ} (hp : 0 < p) {s : ℕ}
    (_hs : p * scaleSum s ≤ 1 / 2)
    (hnext : 1 / 2 < p * scaleSum (s + 1)) :
    (∑ c : Color s,
      colorProb p s c * ((512 : ℝ) ^ 4 / (512 : ℝ) ^ (c.val + 1))) ≤
      5 * (512 : ℝ) ^ 4 * p := by sorry
