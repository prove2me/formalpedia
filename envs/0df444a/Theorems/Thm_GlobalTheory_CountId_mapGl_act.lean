-- Prove2me | Theorems.Thm_GlobalTheory_CountId_mapGl_act
-- name    : GlobalTheory.CountId.mapGl_act
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:02:46.495806+00:00
-- url     : https://prove2.me/theorems/952dd49b-3839-4ed9-86f4-148c3dd24d6e
-- title:
--   Count Id: map Gl act
-- statement:
--   The Count Id construction uses the map Gl act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L36-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L36-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.CountId
open GlobalTheory.JR
variable {r : ℕ} {k k' : Type} [CommRing k] [CommRing k']

theorem GlobalTheory.CountId.mapGl_act (φ : k →+* k') (γ : GL (Fin r) k) (Y : Gl r k) :
    mapGl φ (act γ Y) = act (Matrix.GeneralLinearGroup.map φ γ) (mapGl φ Y) := by sorry
