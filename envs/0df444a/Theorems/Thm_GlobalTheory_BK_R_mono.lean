-- Prove2me | Theorems.Thm_GlobalTheory_BK_R_mono
-- name    : GlobalTheory.BK.R_mono
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:00:32.577412+00:00
-- url     : https://prove2.me/theorems/d7dc617b-8214-4e38-a0ae-d9c21645a11c
-- title:
--   BK: R mono
-- statement:
--   The BK construction uses the R mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L386-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L386-L390

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

theorem GlobalTheory.BK.R_mono (l : ℕ) [Fact l.Prime] {k k' : ℝ} (h : k ≤ k') : R O K l k ≤ R O K l k' := by sorry
