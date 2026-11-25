-- Prove2me | Theorems.Thm_GlobalTheory_T_existsUnique_embedding_eigenspace_sum
-- name    : GlobalTheory.T.existsUnique_embedding_eigenspace_sum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:28:50.36071+00:00
-- url     : https://prove2.me/theorems/4b6b95a8-0fd4-5f51-a199-c851379380f4
-- title:
--   T: exists Unique embedding eigenspace sum
-- statement:
--   The T construction uses the exists Unique embedding eigenspace sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsUniqueEmbeddingEigenspaceSumStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsUniqueEmbeddingEigenspaceSumStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUniqueEmbeddingEigenspaceSum
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_EmbKCoe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUniqueEmbeddingEigenspaceSumStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.existsUnique_embedding_eigenspace_sum : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (φ : c.F →+* R) (ρ : 𝓞 E →+* Module.End R V) (v : V), ∃! w : (E →+* ℂ) → V, (∀ τ a, ρ a (w τ) = φ (embK c τ a) • w τ) ∧ ∑ τ, w τ = v := by sorry
