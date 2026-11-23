-- Prove2me | Theorems.Thm_GlobalTheory_BK_mem_R
-- name    : GlobalTheory.BK.mem_R
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:29.62782+00:00
-- url     : https://prove2.me/theorems/25c0a1a4-cb5f-400a-b409-e13b4f4425c2
-- title:
--   BK: mem R
-- statement:
--   The BK construction uses the mem R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L169-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L169-L171

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

theorem GlobalTheory.BK.mem_R {l : ℕ} {k : ℝ} {f : K⟦X⟧} :
    f ∈ R O K l k ↔ Tendsto (fun n => ‖coeff n f‖ * rad l k ^ n) atTop (𝓝 0) := by sorry
