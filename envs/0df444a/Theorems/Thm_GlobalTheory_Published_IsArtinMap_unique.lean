-- Prove2me | Theorems.Thm_GlobalTheory_Published_IsArtinMap_unique
-- name    : GlobalTheory.Published.IsArtinMap.unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:54.891452+00:00
-- url     : https://prove2.me/theorems/4fe33014-85d9-4997-bea5-5534f78bec10
-- title:
--   Is Artin Map: unique
-- statement:
--   The Is Artin Map construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/ComplexMultiplicationJPremises.lean#L85-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/ComplexMultiplicationJPremises.lean#L85-L112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors IntermediateField
open GlobalTheory GlobalTheory.Published
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]

theorem GlobalTheory.Published.IsArtinMap.unique {H : IntermediateField K ℂ} (hH : IsUnramifiedAbelian H)
    {f g : ClassGroup (𝓞 K) →* (H ≃ₐ[K] H)} (hf : IsArtinMap f) (hg : IsArtinMap g) : f = g := by sorry
