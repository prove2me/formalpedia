-- Prove2me | Theorems.Thm_GlobalTheory_linearIndependent_ringHom_comp_iff
-- name    : GlobalTheory.linearIndependent_ringHom_comp_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:20:36.850007+00:00
-- url     : https://prove2.me/theorems/23cf4b48-9e5d-4476-ac08-7f6ca5d412eb
-- title:
--   Global Theory: linear Independent ring Hom comp iff
-- statement:
--   The Global Theory construction uses the linear Independent ring Hom comp iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LinearIndependentRingHomCompIff.lean#L5-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LinearIndependentRingHomCompIff.lean#L5-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LinearIndependentRingHomCompIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.linearIndependent_ringHom_comp_iff {A F : Type} [CommRing A] [Field F] (φ : A →+* F)
    (hφ : Function.Injective φ) {ι μ : Type} [Finite μ] (c : ι → μ → A) :
    LinearIndependent F (fun i m => φ (c i m)) ↔ LinearIndependent A c := by sorry
