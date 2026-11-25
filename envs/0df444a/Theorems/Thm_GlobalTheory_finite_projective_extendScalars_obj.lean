-- Prove2me | Theorems.Thm_GlobalTheory_finite_projective_extendScalars_obj
-- name    : GlobalTheory.finite_projective_extendScalars_obj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:50:03.590468+00:00
-- url     : https://prove2.me/theorems/6f24726c-619b-4326-9a86-88095c3913e2
-- title:
--   Global Theory: finite projective extend Scalars obj
-- statement:
--   The Global Theory construction uses the finite projective extend Scalars obj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexOfNoetherianModel.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexOfNoetherianModel.lean#L17-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexOfNoetherianModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory

theorem GlobalTheory.finite_projective_extendScalars_obj {R₀ R : Type} [CommRing R₀] [CommRing R]
    (f : R₀ →+* R) (M : ModuleCat.{0} R₀) [Module.Finite R₀ M] [Module.Projective R₀ M] :
    Module.Finite R ((ModuleCat.extendScalars.{0, 0, 0} f).obj M) ∧
      Module.Projective R ((ModuleCat.extendScalars.{0, 0, 0} f).obj M) := by sorry
