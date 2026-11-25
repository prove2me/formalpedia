-- Prove2me | Theorems.Thm_GlobalTheory_CountId_Inv_map_injective
-- name    : GlobalTheory.CountId.Inv_map_injective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:02:32.770342+00:00
-- url     : https://prove2.me/theorems/b4b731aa-6004-5302-93ee-d9b04e0cf189
-- title:
--   Count Id: Inv map injective
-- statement:
--   The Count Id construction uses the Inv map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L73-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L73-L78

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

theorem GlobalTheory.CountId.Inv_map_injective (φ : k →+* k') (h : Function.Injective φ) :
    Function.Injective (fun a : Inv r k => a.map φ) := by sorry
