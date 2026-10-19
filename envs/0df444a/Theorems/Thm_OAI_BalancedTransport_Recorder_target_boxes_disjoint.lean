-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Recorder_target_boxes_disjoint
-- name    : OAI.BalancedTransport.Recorder.target_boxes_disjoint
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:10:11.558004+00:00
-- url     : https://prove2.me/theorems/7fd5b5bc-52ae-42fc-9f6a-91226d76ec68
-- title:
--   Target boxes of distinct recorder rows are disjoint
-- statement:
--   Each row of the recorder's table determines an instruction with a source control, a target control, and source and target prefixes for the three stacks. Given a ratio $r>0$, a digit map $\delta$ on stack letters and a numbering $\mathrm{id}$ of control states, the source box of an instruction is
--   $$
--   \bigl\{x\in\mathbb R^3: x_k-o_k\in I(u_k)\text{ for }k=0,1,2\bigr\},
--   $$
--   where $o=(4\,\mathrm{id}(\text{source control}),0,0)$, $u_0,u_1,u_2$ are the source prefixes and $I(u)$ is the base-$r$ coding interval of $u$. Target boxes are defined in the same way from the target data.
--
--   Assume $r>0$, $\delta\ge0$, $r(\delta(a)+1)\le1$ for every letter, digits of distinct letters differ by more than $1$, and $\mathrm{id}$ is injective. Then distinct rows, valid or not, have disjoint target boxes. So every coded configuration is reached by at most one row, which makes the box dynamics reversible.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/BoxCoding.lean#L312-L338

import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding

open OAI OAI.BalancedTransport OAI.BalancedTransport.Recorder
variable {Q Γ : Type*}

theorem OAI.BalancedTransport.Recorder.target_boxes_disjoint (M : Machine Q Γ)
    {r : ℝ} (hr : 0 < r) (digit : Letter Q Γ → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    (hgap : ∀ a b, a ≠ b → digit a + 1 < digit b ∨ digit b + 1 < digit a)
    (id : Control Q → ℕ) (hid : Function.Injective id)
    {a b : Row Q Γ} (hab : a ≠ b) :
    Disjoint ((a.instruction M).targetBox r digit id)
      ((b.instruction M).targetBox r digit id) := by sorry
