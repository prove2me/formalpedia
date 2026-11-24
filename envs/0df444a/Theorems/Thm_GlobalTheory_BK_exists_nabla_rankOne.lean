-- Prove2me | Theorems.Thm_GlobalTheory_BK_exists_nabla_rankOne
-- name    : GlobalTheory.BK.exists_nabla_rankOne
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:29:48.530334+00:00
-- url     : https://prove2.me/theorems/8e48263b-fc33-4ac7-b934-1f5b30ce504c
-- title:
--   BK: exists nabla rank One
-- statement:
--   The BK construction uses the exists nabla rank One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqMulAddOfIsAdicComplete.lean#L156-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqMulAddOfIsAdicComplete.lean#L156-L205

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemSpanLPowSIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
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
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ) {a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
variable {l e}
variable [CompleteSpace K]

theorem GlobalTheory.BK.exists_nabla_rankOne (j : ℤ) : ∃ γ ∈ S O K e,
    (rankOne O K l e fun _ : ZMod a => j).nabla (Ezpow K l e j • bas ()) =
      γ • Ezpow K l e j • bas () := by sorry
