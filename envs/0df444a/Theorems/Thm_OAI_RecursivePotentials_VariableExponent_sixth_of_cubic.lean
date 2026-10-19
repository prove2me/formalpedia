-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_VariableExponent_sixth_of_cubic
-- name    : OAI.RecursivePotentials.VariableExponent.sixth_of_cubic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T08:21:52.761875+00:00
-- url     : https://prove2.me/theorems/0242c0df-af6b-4f0e-b8c1-1fc144df028d
-- title:
--   From a cubic midpoint gap to a sixth-power bound on the quadratic gap
-- statement:
--   Let $c_3=(6e)^{-3}$ and $c_6=2e^{-(e-1)}\,4^{-6}$. Let $a,b,B,Y$ be nonnegative real numbers such that $B\le\frac{a+b}{2}$ and $Y\le\frac{a+b}{2}$, and suppose that
--   $$
--   c_3\,Y^3\le\Bigl(\frac{a+b}{2}-B\Bigr)\max(a,b)^2 .
--   $$
--   Then
--   $$
--   c_6\,Y^6\le\bigl(a^2+b^2-2B^2\bigr)\bigl(a^2+b^2\bigr)^2 .
--   $$
--
--   The lemma is designed for $a=\|x+y\|$, $b=\|x-y\|$, $B=\|x\|$ and $Y=\|y\|$ in a normed space, where the two side conditions follow from the triangle inequality. It converts a cubic midpoint-gap inequality $c_3\|y\|^3\le\bigl(\frac{\|x+y\|+\|x-y\|}{2}-\|x\|\bigr)\max(\|x+y\|,\|x-y\|)^2$ into a lower bound for the quadratic gap $\|x+y\|^2+\|x-y\|^2-2\|x\|^2$. Unlike the linear midpoint gap, the quadratic gap and the quantities $\|y\|^2$ and $\|x+y\|^2+\|x-y\|^2$ are additive over $\ell^2$-direct sums, so the converted inequality can be summed over the components of an $\ell^2$-sum to give a sixth-power stability estimate there.
--
--   **Formalization Note** $c_3$ is `cubicConstant` and $c_6$ is `sixthConstant`; the statement is about plain real numbers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/VariableCompletion.lean#L437-L476

import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms
import Definitions.Def_OAI_Analysis_RecursivePotentials_JoinedGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableEstimates
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableCompletion

open OAI OAI.RecursivePotentials OAI.RecursivePotentials.VariableExponent
universe uIndex uSpace uOther uDomain uTarget uFiber
open scoped BigOperators
open Filter Topology
open Filter Topology
open scoped ENNReal
open UniformSpace
open Filter
open scoped Topology

theorem OAI.RecursivePotentials.VariableExponent.sixth_of_cubic {a b B Y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hB : 0 ≤ B) (hY : 0 ≤ Y)
    (hBm : B ≤ (a+b)/2) (hYm : Y ≤ (a+b)/2)
    (hcubic : cubicConstant * Y ^ 3 ≤ ((a+b)/2-B) * max a b ^ 2) :
    sixthConstant * Y ^ 6 ≤ (a^2+b^2-2*B^2) * (a^2+b^2)^2 := by sorry
