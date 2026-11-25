-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_continuous_sigR
-- name    : GlobalTheory.RegSS.continuous_sigR
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:20:59.334449+00:00
-- url     : https://prove2.me/theorems/608b182a-b0bc-41a0-bda6-6c0261e3f2c0
-- title:
--   Reg SS: continuous sig R
-- statement:
--   The Reg SS construction uses the continuous sig R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L608-L619
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L608-L619

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

theorem GlobalTheory.RegSS.continuous_sigR (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] :
    @Continuous _ _ (_root_.Formalism.BasicNotions.tensTopL (F := F) (E := E) R) (_root_.Formalism.BasicNotions.tensTopL (F := F) (E := E) R)
      (_root_.Formalism.UG.sigR σ R) := by sorry
