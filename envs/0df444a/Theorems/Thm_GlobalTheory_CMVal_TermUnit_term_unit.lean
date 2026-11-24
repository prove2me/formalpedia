-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_TermUnit_term_unit
-- name    : GlobalTheory.CMVal.TermUnit.term_unit
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:06:24.606824+00:00
-- url     : https://prove2.me/theorems/55d2961c-ddf3-487f-9578-44777f499c0c
-- title:
--   Term Unit: term unit
-- statement:
--   The Term Unit construction uses the term unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdNormSq.lean#L46-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdNormSq.lean#L46-L81

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

theorem GlobalTheory.CMVal.TermUnit.term_unit [IsCMField E] {φ : I → E →+* ℂ} (h : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) (u : (OF E)ˣ) :
    term φ (2 * s) κ σ (algebraMap (OF E) E u) = 1 := by sorry
