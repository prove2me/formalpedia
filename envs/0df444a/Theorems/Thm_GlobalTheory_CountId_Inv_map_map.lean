-- Prove2me | Theorems.Thm_GlobalTheory_CountId_Inv_map_map
-- name    : GlobalTheory.CountId.Inv_map_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:02:24.974848+00:00
-- url     : https://prove2.me/theorems/c57ab718-84a8-5d5a-8191-604d659dc29f
-- title:
--   Count Id: Inv map map
-- statement:
--   The Count Id construction uses the Inv map map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L70-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L70-L71

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

theorem GlobalTheory.CountId.Inv_map_map {k'' : Type} [CommRing k''] (φ : k →+* k') (ψ : k' →+* k'') (a : Inv r k) :
    (a.map φ).map ψ = a.map (ψ.comp φ) := by sorry
