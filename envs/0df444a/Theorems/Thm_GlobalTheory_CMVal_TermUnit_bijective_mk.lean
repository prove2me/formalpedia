-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_TermUnit_bijective_mk
-- name    : GlobalTheory.CMVal.TermUnit.bijective_mk
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:06:21.016268+00:00
-- url     : https://prove2.me/theorems/fb22bdf6-42fa-4640-a321-edddd5184c98
-- title:
--   Term Unit: bijective mk
-- statement:
--   The Term Unit construction uses the bijective mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdNormSq.lean#L13-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdNormSq.lean#L13-L28

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdNormSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.TermUnit
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
omit [NumberField E] [Fintype I]

theorem GlobalTheory.CMVal.TermUnit.bijective_mk {φ : I → E →+* ℂ} (h : IsCMType φ) :
    Function.Bijective (fun i => InfinitePlace.mk (φ i)) := by sorry
