-- Prove2me | Theorems.Thm_GroundTheory_LocalField_algebraMap_norm_eq_prod_embeddings_of_splits
-- name    : GroundTheory.LocalField.algebraMap_norm_eq_prod_embeddings_of_splits
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:17:17.393807+00:00
-- url     : https://prove2.me/theorems/75e3478d-7738-422d-8447-c8a028686306
-- title:
--   Local Field: algebra Map norm eq prod embeddings of splits
-- statement:
--   The Local Field construction uses the algebra Map norm eq prod embeddings of splits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalAxiomDictionary.lean#L15-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalAxiomDictionary.lean#L15-L33

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomTransport
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomDictionary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Abstract IntermediateField
variable (K L Ω : Type*) [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

theorem GroundTheory.LocalField.algebraMap_norm_eq_prod_embeddings_of_splits
    (hL : ∀ x : L, ((minpoly K x).map (algebraMap K Ω)).Splits) (x : L) :
    haveI : Fintype (L →ₐ[K] Ω) := Fintype.ofFinite _
    algebraMap K Ω (Algebra.norm K x) = ∏ τ : L →ₐ[K] Ω, τ x := by sorry
