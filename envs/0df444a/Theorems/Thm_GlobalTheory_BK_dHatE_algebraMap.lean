-- Prove2me | Theorems.Thm_GlobalTheory_BK_dHatE_algebraMap
-- name    : GlobalTheory.BK.dHatE_algebraMap
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:02:45.800645+00:00
-- url     : https://prove2.me/theorems/16f5d6de-df16-41bd-8217-da13bfe26aa5
-- title:
--   BK: d Hat E algebra Map
-- statement:
--   The BK construction uses the d Hat E algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/SndDualLiftAlgebraMap.lean#L427-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/SndDualLiftAlgebraMap.lean#L427-L428

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

theorem GlobalTheory.BK.dHatE_algebraMap (x : Ahat O K l e) :
    dHatE O K l e (algebraMap _ _ x) = algebraMap _ _ (dHat O K l e x) := by sorry
