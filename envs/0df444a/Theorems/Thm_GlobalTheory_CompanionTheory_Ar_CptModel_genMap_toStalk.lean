-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_genMap_toStalk
-- name    : GlobalTheory.CompanionTheory.Ar.CptModel.genMap_toStalk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:41.311088+00:00
-- url     : https://prove2.me/theorems/010177ac-dc5a-432e-9543-9478f823e642
-- title:
--   Cpt Model: gen Map to Stalk
-- statement:
--   The Cpt Model construction uses the gen Map to Stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L69-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L69-L82

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

theorem GlobalTheory.CompanionTheory.Ar.CptModel.genMap_toStalk (φ : R →+* K) (p : Cpt (pt φ)) (r : R) :
    genMap (pt φ) p (tS p.1 r) = φ r := by sorry
