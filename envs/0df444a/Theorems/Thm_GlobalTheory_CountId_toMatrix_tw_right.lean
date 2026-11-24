-- Prove2me | Theorems.Thm_GlobalTheory_CountId_toMatrix_tw_right
-- name    : GlobalTheory.CountId.toMatrix_tw_right
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:26:27.601379+00:00
-- url     : https://prove2.me/theorems/958011d0-4214-4a13-98d0-f992a5d2d094
-- title:
--   Count Id: to Matrix tw right
-- statement:
--   The Count Id construction uses the to Matrix tw right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L112-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L112-L115

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

theorem GlobalTheory.CountId.toMatrix_tw_right (e : Basis (Fin n) E V) (γ : GL (Fin n) E) :
    e.toMatrix (tw e γ) = ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by sorry
