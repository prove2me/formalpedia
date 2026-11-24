-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_mem_regAt_iff
-- name    : GlobalTheory.CompanionTheory.Ar.CptModel.mem_regAt_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:15.926283+00:00
-- url     : https://prove2.me/theorems/9e2fc99c-8d0c-4860-b3c1-b502b24dd389
-- title:
--   Cpt Model: mem reg At iff
-- statement:
--   The Cpt Model construction uses the mem reg At iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L98-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L98-L117

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

theorem GlobalTheory.CompanionTheory.Ar.CptModel.mem_regAt_iff (φ : R →+* K) (p : Cpt (pt φ)) (c : K) :
    c ∈ regAt (pt φ) p ↔ ∃ a s : R, s ∉ p.1.asIdeal ∧ φ s ≠ 0 ∧ c * φ s = φ a := by sorry
