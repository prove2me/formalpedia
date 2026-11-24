-- Prove2me | Theorems.Thm_GlobalTheory_TraceConj_colRep_semisimple
-- name    : GlobalTheory.TraceConj.colRep_semisimple
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:12:08.379249+00:00
-- url     : https://prove2.me/theorems/6f822e4c-f3d0-4959-bb36-b748a166ea87
-- title:
--   Trace Conj: col Rep semisimple
-- statement:
--   The Trace Conj construction uses the col Rep semisimple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ColRepSemisimple.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ColRepSemisimple.lean#L23-L31

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

theorem GlobalTheory.TraceConj.colRep_semisimple (ρ : Γ →* GL (Fin a) k) (h : Formalism.MainNotions.N.IsSSRep ρ) :
    (colRep ρ).IsSemisimpleRepresentation := by sorry
