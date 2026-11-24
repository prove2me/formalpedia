-- Prove2me | Theorems.Thm_GlobalTheory_BK_invE_le_RpiE
-- name    : GlobalTheory.BK.invE_le_RpiE
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:35:55.666263+00:00
-- url     : https://prove2.me/theorems/70cf1daf-a44b-458e-8f3c-2f9d346057c8
-- title:
--   BK: inv E le Rpi E
-- statement:
--   The BK construction uses the inv E le Rpi E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/SndDualLiftAlgebraMap.lean#L477-L478
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/SndDualLiftAlgebraMap.lean#L477-L478

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DerivationMemPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
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
  [IsUnitBall O K] (l e : ℕ)
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
variable [NeZero e] [CompleteSpace K]
variable {O K}

theorem GlobalTheory.BK.invE_le_RpiE {B : Subalgebra O K⟦X⟧} [HasU B] (h : B ≤ Rpi O K l e) :
    invE l e B ≤ RpiE O K l e := by sorry
