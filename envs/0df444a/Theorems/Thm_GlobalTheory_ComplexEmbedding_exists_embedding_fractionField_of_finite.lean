-- Prove2me | Theorems.Thm_GlobalTheory_ComplexEmbedding_exists_embedding_fractionField_of_finite
-- name    : GlobalTheory.ComplexEmbedding.exists_embedding_fractionField_of_finite
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:13:52.561262+00:00
-- url     : https://prove2.me/theorems/e3b7fc8a-3945-49a1-9c4f-04ea32455204
-- title:
--   Complex Embedding: exists embedding fraction Field of finite
-- statement:
--   The Complex Embedding construction uses the exists embedding fraction Field of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsComplexEmbeddingFractionFieldFiniteOverCdv.lean#L64-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsComplexEmbeddingFractionFieldFiniteOverCdv.lean#L64-L81

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComplexEmbeddingFractionFieldCdvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComplexEmbeddingFractionFieldFiniteOverCdv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.L2.Pj
open GlobalTheory GlobalTheory.ComplexEmbedding
open Cardinal IsLocalRing

theorem GlobalTheory.ComplexEmbedding.exists_embedding_fractionField_of_finite :
    ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (T T' : CDVR) (g : T.V →+* T'.V),
      Function.Injective g → g.Finite → Countable (IsLocalRing.ResidueField T.V) →
      ∀ io : K →+* T'.Fr, ∃ ι : T'.Fr →+* ℂ, ι.comp io = σ := by sorry
