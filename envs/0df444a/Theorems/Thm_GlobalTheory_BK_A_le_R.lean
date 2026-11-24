-- Prove2me | Theorems.Thm_GlobalTheory_BK_A_le_R
-- name    : GlobalTheory.BK.A_le_R
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:00:35.628538+00:00
-- url     : https://prove2.me/theorems/8360a440-bfeb-4b3d-994d-61fb2a292091
-- title:
--   BK: A le R
-- statement:
--   The BK construction uses the A le R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L392-L395
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L392-L395

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

theorem GlobalTheory.BK.A_le_R (l : ℕ) [Fact l.Prime] {k : ℝ} (hk : 0 < k) : A O K ≤ R O K l k := by sorry
