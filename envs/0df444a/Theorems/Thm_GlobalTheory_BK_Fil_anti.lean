-- Prove2me | Theorems.Thm_GlobalTheory_BK_Fil_anti
-- name    : GlobalTheory.BK.Fil_anti
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:55:33.167618+00:00
-- url     : https://prove2.me/theorems/e02fc88e-06d2-474a-8b86-88bd91b659d6
-- title:
--   BK: Fil anti
-- statement:
--   The BK construction uses the Fil anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L632-L634
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L632-L634

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
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
include l
omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

theorem GlobalTheory.BK.Fil_anti (e : ℕ) {i j : ℕ} (h : i ≤ j) : Fil O K l e j ≤ Fil O K l e i := by sorry
