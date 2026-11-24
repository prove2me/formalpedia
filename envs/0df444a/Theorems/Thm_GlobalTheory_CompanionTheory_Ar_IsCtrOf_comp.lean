-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_IsCtrOf_comp
-- name    : GlobalTheory.CompanionTheory.Ar.IsCtrOf.comp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:17:17.609191+00:00
-- url     : https://prove2.me/theorems/390d3bd1-5c7d-4506-9d13-e689aedf0235
-- title:
--   Is Ctr Of: comp
-- statement:
--   The Is Ctr Of construction uses the comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/GlueApplyOfNotInFibre.lean#L125-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/GlueApplyOfNotInFibre.lean#L125-L127

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

theorem GlobalTheory.CompanionTheory.Ar.IsCtrOf.comp {i : Ω →+* Ω'} {i' : Ω' →+* Ω''} {p : Cpt ξ} {p' : Cpt ξ'} {p'' : Cpt ξ''}
    (h : IsCtrOf i p p') (h' : IsCtrOf i' p' p'') : IsCtrOf (i'.comp i) p p'' := by sorry
