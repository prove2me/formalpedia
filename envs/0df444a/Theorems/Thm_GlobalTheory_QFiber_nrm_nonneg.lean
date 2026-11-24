-- Prove2me | Theorems.Thm_GlobalTheory_QFiber_nrm_nonneg
-- name    : GlobalTheory.QFiber.nrm_nonneg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:02:35.453189+00:00
-- url     : https://prove2.me/theorems/86bde4df-83e6-4985-8b9a-8ccbc9d54476
-- title:
--   QFiber: nrm nonneg
-- statement:
--   The QFiber construction uses the nrm nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardHilbertEisensteinFourierFiberLeNorm.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardHilbertEisensteinFourierFiberLeNorm.lean#L25-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDivisorsLeAbsNormNumberFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardHilbertEisensteinFourierFiberLeNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
noncomputable section
open GlobalTheory GlobalTheory.QFiber
open FractionalIdeal
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.QFiber.nrm_nonneg (𝔞 : Frac F) : 0 ≤ nrm 𝔞 := by sorry
