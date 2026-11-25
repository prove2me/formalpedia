-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Lat_mem_pullLoc_of_ctr
-- name    : GlobalTheory.CompanionTheory.Ar.Lat.mem_pullLoc_of_ctr
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:59:06.822445+00:00
-- url     : https://prove2.me/theorems/71475536-8269-5eba-92ae-94f059299f32
-- title:
--   Lat: mem pull Loc of ctr
-- statement:
--   The Lat construction uses the mem pull Loc of ctr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/GlueApplyOfNotInFibre.lean#L157-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/GlueApplyOfNotInFibre.lean#L157-L159

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

theorem GlobalTheory.CompanionTheory.Ar.Lat.mem_pullLoc_of_ctr {L : Lat ξ E} {i : Ω →+* Ω'} (j : E →+ F) {p : Cpt ξ} {p' : Cpt ξ'}
    (h : IsCtrOf i p p') {e : E} (he : e ∈ L p) : j e ∈ L.pullLoc ξ' i j p' := by sorry
