-- Prove2me | Theorems.Thm_GlobalTheory_EigDecomp_exists_unique_eigen_sum
-- name    : GlobalTheory.EigDecomp.exists_unique_eigen_sum
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:53:20.872781+00:00
-- url     : https://prove2.me/theorems/cbb14582-83c8-4852-a938-8547bafc7d52
-- title:
--   Eig Decomp: exists unique eigen sum
-- statement:
--   The Eig Decomp construction uses the exists unique eigen sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsUniqueEmbeddingEigenspaceSum.lean#L78-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsUniqueEmbeddingEigenspaceSum.lean#L78-L153

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

theorem GlobalTheory.EigDecomp.exists_unique_eigen_sum : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {l : Level H} (c : Coeff l) {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (φ : c.F →+* R)
    (ρ : 𝓞 E →+* Module.End R V) (v : V), ∃! w : (E →+* ℂ) → V,
      (∀ τ a, ρ a (w τ) = φ (embK c τ a) • w τ) ∧ ∑ τ, w τ = v := by sorry
