-- Prove2me | Theorems.Thm_GlobalTheory_BK_invL_le
-- name    : GlobalTheory.BK.invL_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:00:16.958738+00:00
-- url     : https://prove2.me/theorems/c30bc2ec-9716-42c4-bbc8-5ec0973c89f0
-- title:
--   BK: inv L le
-- statement:
--   The BK construction uses the inv L le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L565-L571
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L565-L571

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
omit [IsUltrametricDist K] [IsUnitBall O K]

theorem GlobalTheory.BK.invL_le {B B' : Subalgebra O K⟦X⟧} [HasK B'] (h : B ≤ B') : invL l B ≤ B' := by sorry
