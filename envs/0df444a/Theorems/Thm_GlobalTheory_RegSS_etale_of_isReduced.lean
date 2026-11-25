-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_etale_of_isReduced
-- name    : GlobalTheory.RegSS.etale_of_isReduced
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:27:03.340669+00:00
-- url     : https://prove2.me/theorems/74989f4c-632a-4aa9-b096-63ada6a3be09
-- title:
--   Reg SS: etale of is Reduced
-- statement:
--   The Reg SS construction uses the etale of is Reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L625-L632
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L625-L632

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E}
open Matrix NumberField
open scoped TensorProduct
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E}

theorem GlobalTheory.RegSS.etale_of_isReduced [CharZero F] (B : Type) [CommRing B]
    [Algebra F B] [Module.Finite F B] [IsReduced B] : Algebra.Etale F B := by sorry
