-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_inclE_conj
-- name    : GlobalTheory.RegSS.inclE_conj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:21:44.551133+00:00
-- url     : https://prove2.me/theorems/420cd3da-a1d7-58e8-850d-5b2208e14743
-- title:
--   Reg SS: incl E conj
-- statement:
--   The Reg SS construction uses the incl E conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L559-L561
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L559-L561

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

theorem GlobalTheory.RegSS.inclE_conj (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R]
    (x : E) : _root_.Formalism.UG.inclE (F := F) R (σ x) = _root_.Formalism.UG.sigR σ R (_root_.Formalism.UG.inclE (F := F) R x) := by sorry
