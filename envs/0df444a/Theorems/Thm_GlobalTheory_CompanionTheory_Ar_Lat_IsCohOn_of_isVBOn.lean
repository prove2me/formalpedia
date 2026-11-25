-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Lat_IsCohOn_of_isVBOn
-- name    : GlobalTheory.CompanionTheory.Ar.Lat.IsCohOn.of_isVBOn
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:59:35.275801+00:00
-- url     : https://prove2.me/theorems/a1e4a713-5b7f-480a-898c-1774d6c28b99
-- title:
--   Is Coh On: of is VBOn
-- statement:
--   The Is Coh On construction uses the of is VBOn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/GlueApplyOfNotInFibre.lean#L275-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/GlueApplyOfNotInFibre.lean#L275-L278

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

theorem GlobalTheory.CompanionTheory.Ar.Lat.IsCohOn.of_isVBOn {L : Lat ξ E} {T : Set (Cpt ξ)} {r : ℕ} {V : Submodule Ω E} (h : L.IsVBOn T r V) :
    L.IsCohOn T := by sorry
