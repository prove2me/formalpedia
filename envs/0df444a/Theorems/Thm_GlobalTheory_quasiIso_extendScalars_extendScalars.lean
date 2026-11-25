-- Prove2me | Theorems.Thm_GlobalTheory_quasiIso_extendScalars_extendScalars
-- name    : GlobalTheory.quasiIso_extendScalars_extendScalars
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:50:13.974027+00:00
-- url     : https://prove2.me/theorems/f4ce8e3c-0107-4277-a6d7-01d1d1d8999b
-- title:
--   Global Theory: quasi Iso extend Scalars extend Scalars
-- statement:
--   The Global Theory construction uses the quasi Iso extend Scalars extend Scalars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexOfNoetherianModel.lean#L25-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexOfNoetherianModel.lean#L25-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexOfNoetherianModel
import Theorems.Thm_GlobalTheory_IsGradedMap_comp

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

theorem GlobalTheory.quasiIso_extendScalars_extendScalars {R₀ R R' : Type} [CommRing R₀] [CommRing R]
    [CommRing R'] (f : R₀ →+* R) (g : R →+* R') {K L : CochainComplex (ModuleCat.{0} R₀) ℕ}
    (φ : K ⟶ L)
    (h : QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (g.comp f)).mapHomologicalComplex _).map φ)) :
    QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} g).mapHomologicalComplex _).map
      (((ModuleCat.extendScalars.{0, 0, 0} f).mapHomologicalComplex _).map φ)) := by sorry
