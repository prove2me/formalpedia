-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Lat_glue_apply_of_inFibre
-- name    : GlobalTheory.CompanionTheory.Ar.Lat.glue_apply_of_inFibre
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:59:01.460806+00:00
-- url     : https://prove2.me/theorems/54a7e7e3-9b1d-4059-a701-9e5a79582e38
-- title:
--   Lat: glue apply of in Fibre
-- statement:
--   The Lat construction uses the glue apply of in Fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/GlueApplyOfNotInFibre.lean#L296-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/GlueApplyOfNotInFibre.lean#L296-L304

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

theorem GlobalTheory.CompanionTheory.Ar.Lat.glue_apply_of_inFibre {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) (L₀ : Lat ξ E) (Lq : ℕ → Lat ξ E)
    {q : ℕ} (hq : q ∈ S) {p : Cpt ξ} (hp : InFibre ξ q p) : Lat.glue S L₀ Lq p = Lq q p := by sorry
