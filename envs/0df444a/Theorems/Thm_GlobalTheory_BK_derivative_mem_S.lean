-- Prove2me | Theorems.Thm_GlobalTheory_BK_derivative_mem_S
-- name    : GlobalTheory.BK.derivative_mem_S
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:06:57.11629+00:00
-- url     : https://prove2.me/theorems/934c76d1-6f90-4ee3-9a94-a12b24007a9a
-- title:
--   BK: derivative mem S
-- statement:
--   The BK construction uses the derivative mem S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L416-L436
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L416-L436

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

theorem GlobalTheory.BK.derivative_mem_S {e : ℕ} {f : K⟦X⟧} (hf : f ∈ S O K e) :
    PowerSeries.derivative K f ∈ S O K e := by sorry
