-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RaySq_conv_real_char
-- name    : GlobalTheory.Hk.RaySq.conv_real_char
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:37:30.665883+00:00
-- url     : https://prove2.me/theorems/a05b6d82-22fe-4fd3-9218-d97e0831c270
-- title:
--   Ray Sq: conv real char
-- statement:
--   The Ray Sq construction uses the conv real char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ConvRealChar.lean#L361-L416
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ConvRealChar.lean#L361-L416

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ConvRealChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RaySq
variable {K : Type} [Field K] [NumberField K]
variable {M : ℕ} (D : RayData K M)

theorem GlobalTheory.Hk.RaySq.conv_real_char : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (ε : D.G → ℝ), ε 1 = 1 → (∀ g h, ε (g * h) = ε g * ε h) → (∀ g, ε g = 1 ∨ ε g = -1) → ∀ n : ℕ, 0 ≤ ∑ p ∈ n.divisorsAntidiagonal, (∑ g, aRay D g p.1) * ∑ g, ε g * aRay D g p.2 ∧ ∑ g, aRay D g n ≤ ∑ p ∈ (n ^ 2).divisorsAntidiagonal, (∑ g, aRay D g p.1) * ∑ g, ε g * aRay D g p.2 := by sorry
