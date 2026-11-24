-- Prove2me | Theorems.Thm_GlobalTheory_EigDecomp_exists_integral_separating
-- name    : GlobalTheory.EigDecomp.exists_integral_separating
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:53:19.672716+00:00
-- url     : https://prove2.me/theorems/b3039854-265d-49f1-b864-6d2976409b40
-- title:
--   Eig Decomp: exists integral separating
-- statement:
--   The Eig Decomp construction uses the exists integral separating property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsUniqueEmbeddingEigenspaceSum.lean#L10-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsUniqueEmbeddingEigenspaceSum.lean#L10-L40

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_EmbKCoe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUniqueEmbeddingEigenspaceSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial IntermediateField
open GlobalTheory GlobalTheory.EigDecomp

theorem GlobalTheory.EigDecomp.exists_integral_separating (E : Type) [Field E] [NumberField E] :
    ∃ α : 𝓞 E, (∀ τ τ' : E →+* ℂ, τ (α : E) = τ' (α : E) → τ = τ') ∧
      ∀ a : 𝓞 E, ∃ N : ℤ, N ≠ 0 ∧ ∃ g : ℤ[X], aeval α g = N • a := by sorry
