-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_genMap_injective
-- name    : GlobalTheory.CompanionTheory.Ar.CptModel.genMap_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:26.110729+00:00
-- url     : https://prove2.me/theorems/a4047c20-7824-4e70-a1cc-9753b7374d6a
-- title:
--   Cpt Model: gen Map injective
-- statement:
--   The Cpt Model construction uses the gen Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L124-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L124-L133

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.CptModel
open AlgebraicGeometry CategoryTheory
variable {R K : Type} [CommRing R] [Field K]

theorem GlobalTheory.CompanionTheory.Ar.CptModel.genMap_injective (φ : R →+* K) (hφ : Function.Injective φ) (p : Cpt (pt φ)) :
    Function.Injective (genMap (pt φ) p) := by sorry
