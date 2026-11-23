-- Prove2me | Theorems.Thm_GlobalTheory_BK_mem_S
-- name    : GlobalTheory.BK.mem_S
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:32.961666+00:00
-- url     : https://prove2.me/theorems/1986e33c-b222-4d2f-99bd-b14055a3b587
-- title:
--   BK: mem S
-- statement:
--   The BK construction uses the mem S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L153-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L153-L154

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

theorem GlobalTheory.BK.mem_S {e : ℕ} {f : K⟦X⟧} : f ∈ S O K e ↔ (∀ n, ‖coeff n f‖ * wS K e n ≤ 1) ∧
    Tendsto (fun n => ‖coeff n f‖ * wS K e n) atTop (𝓝 0) := by sorry
