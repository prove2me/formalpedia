-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_complex_embedding_fractionField_finite_over_cdvr
-- name    : GlobalTheory.T.exists_complex_embedding_fractionField_finite_over_cdvr
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:28:44.671862+00:00
-- url     : https://prove2.me/theorems/03865365-298f-4847-959c-d3f0fb9bade5
-- title:
--   T: exists complex embedding fraction Field finite over cdvr
-- statement:
--   The T construction uses the exists complex embedding fraction Field finite over cdvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsComplexEmbeddingFractionFieldFiniteOverCdvStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsComplexEmbeddingFractionFieldFiniteOverCdvStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComplexEmbeddingFractionFieldFiniteOverCdv
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComplexEmbeddingFractionFieldCdvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComplexEmbeddingFractionFieldFiniteOverCdvStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.L2.Pj
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_complex_embedding_fractionField_finite_over_cdvr : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (T T' : CDVR) (g : T.V →+* T'.V), Function.Injective g → g.Finite → Countable (IsLocalRing.ResidueField T.V) → ∀ io : K →+* T'.Fr, ∃ ι : T'.Fr →+* ℂ, ι.comp io = σ := by sorry
