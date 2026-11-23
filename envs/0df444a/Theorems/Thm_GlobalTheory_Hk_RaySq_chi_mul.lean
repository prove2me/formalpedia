-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RaySq_chi_mul
-- name    : GlobalTheory.Hk.RaySq.chi_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:22.323024+00:00
-- url     : https://prove2.me/theorems/f1a7b90b-7930-42a3-bc7e-9f7d0a4437dd
-- title:
--   Ray Sq: chi mul
-- statement:
--   The Ray Sq construction uses the chi mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ConvRealChar.lean#L309-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ConvRealChar.lean#L309-L326

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

theorem GlobalTheory.Hk.RaySq.chi_mul (ε : D.G → ℝ) (hε : ∀ g h, ε (g * h) = ε g * ε h) (I J : Ideal (𝓞 K)) :
    chi D ε (I * J) = chi D ε I * chi D ε J := by sorry
