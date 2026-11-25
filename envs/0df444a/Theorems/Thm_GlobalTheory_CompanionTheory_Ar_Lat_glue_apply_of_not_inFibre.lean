-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Lat_glue_apply_of_not_inFibre
-- name    : GlobalTheory.CompanionTheory.Ar.Lat.glue_apply_of_not_inFibre
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:58:55.725318+00:00
-- url     : https://prove2.me/theorems/a6852878-bd08-5102-864c-2513a0c90dd5
-- title:
--   Lat: glue apply of not in Fibre
-- statement:
--   The Lat construction uses the glue apply of not in Fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/GlueApplyOfNotInFibre.lean#L306-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/GlueApplyOfNotInFibre.lean#L306-L308

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

theorem GlobalTheory.CompanionTheory.Ar.Lat.glue_apply_of_not_inFibre {S : Finset ℕ} (L₀ : Lat ξ E) (Lq : ℕ → Lat ξ E) {p : Cpt ξ}
    (hp : ∀ q ∈ S, ¬ InFibre ξ q p) : Lat.glue S L₀ Lq p = L₀ p := by sorry
