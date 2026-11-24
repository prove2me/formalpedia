-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_HatCap_lattice_one
-- name    : GlobalTheory.CMVal.HatCap.lattice_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:04:23.054618+00:00
-- url     : https://prove2.me/theorems/a57fb66b-9671-44f5-96ef-ff76c2b3dcb0
-- title:
--   Hat Cap: lattice one
-- statement:
--   The Hat Cap construction uses the lattice one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdelicRingClassLatticeOneEqOrder.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdelicRingClassLatticeOneEqOrder.lean#L47-L51

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdelicRingClassLatticeOneEqOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.HatCap
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.HatCap.lattice_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → lattice c 1 = (orderC c : Set E) := by sorry
