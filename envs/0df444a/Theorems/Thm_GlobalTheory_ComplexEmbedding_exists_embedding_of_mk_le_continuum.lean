-- Prove2me | Theorems.Thm_GlobalTheory_ComplexEmbedding_exists_embedding_of_mk_le_continuum
-- name    : GlobalTheory.ComplexEmbedding.exists_embedding_of_mk_le_continuum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:25:24.591559+00:00
-- url     : https://prove2.me/theorems/a0976fc8-4731-4cf8-bec4-023e17b30f12
-- title:
--   Complex Embedding: exists embedding of mk le continuum
-- statement:
--   The Complex Embedding construction uses the exists embedding of mk le continuum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsComplexEmbeddingFractionFieldCdvr.lean#L26-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsComplexEmbeddingFractionFieldCdvr.lean#L26-L50

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComplexEmbeddingFractionFieldCdvr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Pj
open GlobalTheory GlobalTheory.ComplexEmbedding
open Cardinal IsLocalRing

theorem GlobalTheory.ComplexEmbedding.exists_embedding_of_mk_le_continuum {K Ω : Type} [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] (hΩ : #Ω ≤ 𝔠) (σ : K →+* ℂ) :
    ∃ P : Ω →+* ℂ, P.comp (algebraMap K Ω) = σ := by sorry
