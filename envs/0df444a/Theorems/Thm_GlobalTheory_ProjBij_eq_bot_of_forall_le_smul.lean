-- Prove2me | Theorems.Thm_GlobalTheory_ProjBij_eq_bot_of_forall_le_smul
-- name    : GlobalTheory.ProjBij.eq_bot_of_forall_le_smul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:55:46.774734+00:00
-- url     : https://prove2.me/theorems/f41a6779-7756-45db-addb-7484f14807a9
-- title:
--   Proj Bij: eq bot of forall le smul
-- statement:
--   The Proj Bij construction uses the eq bot of forall le smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BijectiveOfInjectiveModMaximal.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BijectiveOfInjectiveModMaximal.lean#L7-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BijectiveOfInjectiveModMaximal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.ProjBij

theorem GlobalTheory.ProjBij.eq_bot_of_forall_le_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (K : Submodule R M) (hK : K.FG) (h : ∀ m : Ideal R, m.IsMaximal → K ≤ m • K) : K = ⊥ := by sorry
