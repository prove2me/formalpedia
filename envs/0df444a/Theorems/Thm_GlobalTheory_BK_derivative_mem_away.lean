-- Prove2me | Theorems.Thm_GlobalTheory_BK_derivative_mem_away
-- name    : GlobalTheory.BK.derivative_mem_away
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:20.957807+00:00
-- url     : https://prove2.me/theorems/71451461-9512-4637-8f1c-d06de97649b1
-- title:
--   BK: derivative mem away
-- statement:
--   The BK construction uses the derivative mem away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L439-L450
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L439-L450

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
omit [IsUltrametricDist K] [IsUnitBall O K]

theorem GlobalTheory.BK.derivative_mem_away {B : Subalgebra O K⟦X⟧} (s : B)
    (hB : ∀ f ∈ B, PowerSeries.derivative K f ∈ B) {f : K⟦X⟧} (hf : f ∈ away B s) :
    PowerSeries.derivative K f ∈ away B s := by sorry
