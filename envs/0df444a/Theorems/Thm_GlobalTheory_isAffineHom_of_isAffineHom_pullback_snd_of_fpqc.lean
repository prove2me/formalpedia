-- Prove2me | Theorems.Thm_GlobalTheory_isAffineHom_of_isAffineHom_pullback_snd_of_fpqc
-- name    : GlobalTheory.isAffineHom_of_isAffineHom_pullback_snd_of_fpqc
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:56:37.942156+00:00
-- url     : https://prove2.me/theorems/9a9647cb-e6b8-4f8b-9a06-ab85b632425c
-- title:
--   Global Theory: is Affine Hom of is Affine Hom pullback snd of fpqc
-- statement:
--   The Global Theory construction uses the is Affine Hom of is Affine Hom pullback snd of fpqc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsAffineHomOfIsAffineHomPullbackSndOfFpqc.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsAffineHomOfIsAffineHomPullbackSndOfFpqc.lean#L10-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsAffineHomOfIsAffineHomPullbackSndOfFpqc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory
open CategoryTheory Limits AlgebraicGeometry

theorem GlobalTheory.isAffineHom_of_isAffineHom_pullback_snd_of_fpqc :
    ∀ (X Y Y' : Scheme.{0}) (f : X ⟶ Y) (g : Y' ⟶ Y), Surjective g → Flat g → QuasiCompact g →
      IsAffineHom (pullback.snd f g) → IsAffineHom f := by sorry
