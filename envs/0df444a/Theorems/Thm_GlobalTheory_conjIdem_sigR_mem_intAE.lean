-- Prove2me | Theorems.Thm_GlobalTheory_conjIdem_sigR_mem_intAE
-- name    : GlobalTheory.conjIdem_sigR_mem_intAE
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:34:19.977832+00:00
-- url     : https://prove2.me/theorems/23143e8c-ad60-4b00-87b0-c358249efcb8
-- title:
--   Global Theory: conj Idem sig R mem int AE
-- statement:
--   The Global Theory construction uses the conj Idem sig R mem int AE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/CmConjugationOnPrimesProperties.lean#L43-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/CmConjugationOnPrimesProperties.lean#L43-L53

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
variable [NumberField F] [NumberField E]
omit [NumberField E]

theorem GlobalTheory.conjIdem_sigR_mem_intAE (σ : E →ₐ[F] E) (h : ∀ x : 𝓞 E, ∃ y : 𝓞 E, (y : E) = σ x)
    (y : Af F ⊗[F] E) (hy : y ∈ intAE F E) : sigR (Af F) σ y ∈ intAE F E := by sorry
