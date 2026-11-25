-- Prove2me | Theorems.Thm_GlobalTheory_ComplexEmbedding_mk_le_continuum_of_countable_residueField
-- name    : GlobalTheory.ComplexEmbedding.mk_le_continuum_of_countable_residueField
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:13:49.873379+00:00
-- url     : https://prove2.me/theorems/aff89dc2-9b37-46ee-a1ee-9958acf2c301
-- title:
--   Complex Embedding: mk le continuum of countable residue Field
-- statement:
--   The Complex Embedding construction uses the mk le continuum of countable residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsComplexEmbeddingFractionFieldFiniteOverCdv.lean#L49-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsComplexEmbeddingFractionFieldFiniteOverCdv.lean#L49-L62

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

theorem GlobalTheory.ComplexEmbedding.mk_le_continuum_of_countable_residueField (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Countable (ResidueField V)] : #V ≤ 𝔠 := by sorry
