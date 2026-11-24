-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_exists_frac
-- name    : GlobalTheory.CompanionTheory.Ar.CptModel.exists_frac
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:29.026994+00:00
-- url     : https://prove2.me/theorems/7c9b98ec-6598-4160-9023-3f0a49f5456e
-- title:
--   Cpt Model: exists frac
-- statement:
--   The Cpt Model construction uses the exists frac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L84-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L84-L91

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

theorem GlobalTheory.CompanionTheory.Ar.CptModel.exists_frac (φ : R →+* K) (p : Cpt (pt φ)) (x : (Spec (CommRingCat.of R)).presheaf.stalk p.1) :
    ∃ a s : R, s ∉ p.1.asIdeal ∧
      x * tS p.1 s = tS p.1 a := by sorry
