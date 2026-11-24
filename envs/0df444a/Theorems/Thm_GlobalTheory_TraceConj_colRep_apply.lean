-- Prove2me | Theorems.Thm_GlobalTheory_TraceConj_colRep_apply
-- name    : GlobalTheory.TraceConj.colRep_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:11:51.939638+00:00
-- url     : https://prove2.me/theorems/4b3987bc-7bae-47e3-a3a6-8c959912e1a9
-- title:
--   Trace Conj: col Rep apply
-- statement:
--   The Trace Conj construction uses the col Rep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ColRepSemisimple.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ColRepSemisimple.lean#L20-L21

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyLinearEquivOfCharpolyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ColRepSemisimple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TraceConj
variable {Γ k : Type} [Group Γ] [Field k] {a : ℕ}

theorem GlobalTheory.TraceConj.colRep_apply (ρ : Γ →* GL (Fin a) k) (g : Γ) :
    colRep ρ g = Matrix.toLin' ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) := by sorry
