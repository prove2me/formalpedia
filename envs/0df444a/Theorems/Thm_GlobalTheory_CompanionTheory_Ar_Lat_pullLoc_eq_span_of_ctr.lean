-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Lat_pullLoc_eq_span_of_ctr
-- name    : GlobalTheory.CompanionTheory.Ar.Lat.pullLoc_eq_span_of_ctr
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:17:13.989478+00:00
-- url     : https://prove2.me/theorems/a224fac3-d881-4513-b8aa-1d356c2e4935
-- title:
--   Lat: pull Loc eq span of ctr
-- statement:
--   The Lat construction uses the pull Loc eq span of ctr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/GlueApplyOfNotInFibre.lean#L161-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/GlueApplyOfNotInFibre.lean#L161-L168

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

theorem GlobalTheory.CompanionTheory.Ar.Lat.pullLoc_eq_span_of_ctr {L : Lat ξ E} {i : Ω →+* Ω'} (j : E →+ F) {p₀ : Cpt ξ} {p' : Cpt ξ'}
    (h : IsCtrOf i p₀ p') (hu : ∀ p : Cpt ξ, IsCtrOf i p p' → ∀ e ∈ L p, e ∈ L p₀) :
    L.pullLoc ξ' i j p' = Submodule.span (regAt ξ' p') (j '' (L p₀ : Set E)) := by sorry
