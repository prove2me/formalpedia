-- Prove2me | Theorems.Thm_GlobalTheory_ComplexEmbedding_countable_quotient_pow_of_dvr
-- name    : GlobalTheory.ComplexEmbedding.countable_quotient_pow_of_dvr
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:14:04.584977+00:00
-- url     : https://prove2.me/theorems/b34ae567-c0c3-43c1-bd68-10d3fb3ae06b
-- title:
--   Complex Embedding: countable quotient pow of dvr
-- statement:
--   The Complex Embedding construction uses the countable quotient pow of dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsComplexEmbeddingFractionFieldFiniteOverCdv.lean#L36-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsComplexEmbeddingFractionFieldFiniteOverCdv.lean#L36-L47

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

theorem GlobalTheory.ComplexEmbedding.countable_quotient_pow_of_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Countable (ResidueField V)] (n : ℕ) : Countable (V ⧸ maximalIdeal V ^ n) := by sorry
