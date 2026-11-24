-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_Nakayama_mem_jacobson
-- name    : GlobalTheory.UnRep.Nakayama.mem_jacobson
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:04:15.189829+00:00
-- url     : https://prove2.me/theorems/f802afeb-448f-4dfb-a379-a10981594e2e
-- title:
--   Nakayama: mem jacobson
-- statement:
--   The Nakayama construction uses the mem jacobson property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsInverseOneAddPreservingAdelicCompletion.lean#L24-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsInverseOneAddPreservingAdelicCompletion.lean#L24-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInverseOneAddPreservingAdelicCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.Nakayama
variable (F : Type) [Field F] [NumberField F]
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix
variable (F : Type) [Field F] [NumberField F]

theorem GlobalTheory.UnRep.Nakayama.mem_jacobson (a : _root_.GlobalTheory.UnRep.Nakayama.intAdeles F)
    (ha : ∀ v, Valued.v (a.1 v) < 1) :
    a ∈ Ideal.jacobson (⊥ : Ideal (_root_.GlobalTheory.UnRep.Nakayama.intAdeles F)) := by sorry
