-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Lat_pullLoc_id_spec
-- name    : GlobalTheory.CompanionTheory.Ar.Lat.pullLoc_id_spec
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:01:01.230013+00:00
-- url     : https://prove2.me/theorems/cfa8b5b0-6c69-4584-aac6-af7842426a6b
-- title:
--   Lat: pull Loc id spec
-- statement:
--   The Lat construction uses the pull Loc id spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/GlueApplyOfNotInFibre.lean#L179-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/GlueApplyOfNotInFibre.lean#L179-L184

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsGenOfIsVBOne
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StalkClosedPointToToStalk
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_GlueApplyOfNotInFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory
variable {X X' X'' : Scheme.{0}} {Ω Ω' Ω'' : Type} [Field Ω] [Field Ω'] [Field Ω'']
  {E F : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup F] [Module Ω' F]
variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
  {ξ'' : Spec (CommRingCat.of Ω'') ⟶ X''}

theorem GlobalTheory.CompanionTheory.Ar.Lat.pullLoc_id_spec {R : Type} [CommRing R] {φ : R →+* Ω} (hφ : Function.Injective φ)
    (L : Lat (CptModel.pt φ) E) : L.pullLoc (CptModel.pt φ) (RingHom.id Ω) (AddMonoidHom.id E) = L := by sorry
