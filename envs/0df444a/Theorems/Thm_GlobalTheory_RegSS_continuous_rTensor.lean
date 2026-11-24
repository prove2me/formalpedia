-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_continuous_rTensor
-- name    : GlobalTheory.RegSS.continuous_rTensor
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:20:36.968857+00:00
-- url     : https://prove2.me/theorems/eebe51d1-63cd-4571-80e6-73906edac6e0
-- title:
--   Reg SS: continuous r Tensor
-- statement:
--   The Reg SS construction uses the continuous r Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L577-L603
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L577-L603

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

theorem GlobalTheory.RegSS.continuous_rTensor {B B' : Type} [CommRing B] [Algebra F B]
    [CommRing B'] [Algebra F B'] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    (f : B →ₗ[F] B') :
    @Continuous _ _ (_root_.Formalism.BasicNotions.tensTopL (F := F) (E := B) R) (_root_.Formalism.BasicNotions.tensTopL (F := F) (E := B') R)
      (LinearMap.rTensor R f) := by sorry
