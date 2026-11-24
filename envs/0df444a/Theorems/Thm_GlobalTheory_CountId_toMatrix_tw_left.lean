-- Prove2me | Theorems.Thm_GlobalTheory_CountId_toMatrix_tw_left
-- name    : GlobalTheory.CountId.toMatrix_tw_left
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:26:30.016553+00:00
-- url     : https://prove2.me/theorems/f872dc49-e1d8-40bf-a4a2-efc8ab76c876
-- title:
--   Count Id: to Matrix tw left
-- statement:
--   The Count Id construction uses the to Matrix tw left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L106-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L106-L110

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
variable {n : ℕ} {E V : Type} [Field E] [AddCommGroup V] [Module E V]

theorem GlobalTheory.CountId.toMatrix_tw_left (e : Basis (Fin n) E V) (γ : GL (Fin n) E) :
    (tw e γ).toMatrix e = (γ : Matrix (Fin n) (Fin n) E) := by sorry
