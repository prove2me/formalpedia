-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Lat_pullLoc_congr_ctr
-- name    : GlobalTheory.CompanionTheory.Ar.Lat.pullLoc_congr_ctr
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:01:03.878884+00:00
-- url     : https://prove2.me/theorems/9d2e930e-30fe-4a87-b4d5-0658912ac458
-- title:
--   Lat: pull Loc congr ctr
-- statement:
--   The Lat construction uses the pull Loc congr ctr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/GlueApplyOfNotInFibre.lean#L170-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/GlueApplyOfNotInFibre.lean#L170-L173

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

theorem GlobalTheory.CompanionTheory.Ar.Lat.pullLoc_congr_ctr {L L' : Lat ξ E} {i : Ω →+* Ω'} (j : E →+ F) {p' : Cpt ξ'}
    (h : ∀ p : Cpt ξ, IsCtrOf i p p' → L p = L' p) : L.pullLoc ξ' i j p' = L'.pullLoc ξ' i j p' := by sorry
