-- Prove2me | Theorems.Thm_GlobalTheory_BK_le_normR
-- name    : GlobalTheory.BK.le_normR
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:56:18.331059+00:00
-- url     : https://prove2.me/theorems/de369333-0af4-566e-ba39-a25878889b1a
-- title:
--   BK: le norm R
-- statement:
--   The BK construction uses the le norm R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L178-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L178-L180

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

theorem GlobalTheory.BK.le_normR {l : ℕ} {k : ℝ} {f : K⟦X⟧} (hf : f ∈ R O K l k) (n : ℕ) :
    ‖coeff n f‖ * rad l k ^ n ≤ normR l k f := by sorry
