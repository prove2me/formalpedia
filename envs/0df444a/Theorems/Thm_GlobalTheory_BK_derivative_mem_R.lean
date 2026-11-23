-- Prove2me | Theorems.Thm_GlobalTheory_BK_derivative_mem_R
-- name    : GlobalTheory.BK.derivative_mem_R
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:22.638815+00:00
-- url     : https://prove2.me/theorems/d5a0efcd-fd65-4434-8972-c555e4e925f8
-- title:
--   BK: derivative mem R
-- statement:
--   The BK construction uses the derivative mem R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L406-L414
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L406-L414

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K]
variable {O K}

theorem GlobalTheory.BK.derivative_mem_R (l : ℕ) [Fact l.Prime] {k : ℝ} {f : K⟦X⟧} (hf : f ∈ R O K l k) :
    PowerSeries.derivative K f ∈ R O K l k := by sorry
