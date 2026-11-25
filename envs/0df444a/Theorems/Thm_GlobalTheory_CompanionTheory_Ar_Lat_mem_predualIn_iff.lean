-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Lat_mem_predualIn_iff
-- name    : GlobalTheory.CompanionTheory.Ar.Lat.mem_predualIn_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:59:42.795246+00:00
-- url     : https://prove2.me/theorems/d95de2de-a49f-4929-878c-33d3c269df41
-- title:
--   Lat: mem predual In iff
-- statement:
--   The Lat construction uses the mem predual In iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/GlueApplyOfNotInFibre.lean#L310-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/GlueApplyOfNotInFibre.lean#L310-L311

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

theorem GlobalTheory.CompanionTheory.Ar.Lat.mem_predualIn_iff {L : Lat ξ (Module.Dual Ω E)} {V : Submodule Ω E} {p : Cpt ξ} {v : E} :
    v ∈ L.predualIn V p ↔ v ∈ V ∧ ∀ w ∈ L p, w v ∈ regAt ξ p := by sorry
