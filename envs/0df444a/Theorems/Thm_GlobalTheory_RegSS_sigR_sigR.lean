-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_sigR_sigR
-- name    : GlobalTheory.RegSS.sigR_sigR
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:20:42.021178+00:00
-- url     : https://prove2.me/theorems/53c880ef-8321-4b15-8b56-767032a0bea3
-- title:
--   Reg SS: sig R sig R
-- statement:
--   The Reg SS construction uses the sig R sig R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L566-L571
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L566-L571

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

theorem GlobalTheory.RegSS.sigR_sigR (hσ : ∀ x, σ (σ x) = x) (R : Type) [CommRing R]
    [Algebra F R] (x : E ⊗[F] R) : _root_.Formalism.UG.sigR σ R (_root_.Formalism.UG.sigR σ R x) = x := by sorry
