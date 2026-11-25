-- Prove2me | Theorems.Thm_GlobalTheory_smul_away_bijective
-- name    : GlobalTheory.smul_away_bijective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:43:02.427343+00:00
-- url     : https://prove2.me/theorems/a348c798-0fa5-471a-8e05-a13529b13c41
-- title:
--   Global Theory: smul away bijective
-- statement:
--   The Global Theory construction uses the smul away bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsAwayFracOfMemHomLoc.lean#L72-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsAwayFracOfMemHomLoc.lean#L72-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open DirectSum MvPolynomial CategoryTheory
universe u
noncomputable section
open GlobalTheory
open GradedHilbert
variable {A : Type*} [CommRing A] (M : Type*) [AddCommGroup M] [Module A M]
  {N : Type*} [AddCommGroup N] [Module A N] {P : Type*} [AddCommGroup P] [Module A P]
variable {M}

theorem GlobalTheory.smul_away_bijective {f g : A} {k : ℕ} (h : f ∣ g ^ k) :
    Function.Bijective (LinearMap.lsmul A (LocalizedModule.Away g M) f) := by sorry
