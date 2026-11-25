-- Prove2me | Theorems.Thm_GlobalTheory_conjIdem_sigR_algebraMap
-- name    : GlobalTheory.conjIdem_sigR_algebraMap
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:34:07.224207+00:00
-- url     : https://prove2.me/theorems/64e70183-ee12-47ae-b1a5-d9d92e2dc9e2
-- title:
--   Global Theory: conj Idem sig R algebra Map
-- statement:
--   The Global Theory construction uses the conj Idem sig R algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/CmConjugationOnPrimesProperties.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/CmConjugationOnPrimesProperties.lean#L24-L27

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_ThmBInHecke
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPrimeInvolutionOfRingInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CmConjugationOnPrimesProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors
open GlobalTheory
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem GlobalTheory.conjIdem_sigR_algebraMap (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (a : R) :
    sigR R σ (algebraMap R (R ⊗[F] E) a) = algebraMap R (R ⊗[F] E) a := by sorry
