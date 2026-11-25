-- Prove2me | Theorems.Thm_GlobalTheory_ComplexEmbedding_exists_digits_of_dvr
-- name    : GlobalTheory.ComplexEmbedding.exists_digits_of_dvr
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:13:51.190957+00:00
-- url     : https://prove2.me/theorems/c9e5c885-648c-474c-a3f4-49e37f8f7838
-- title:
--   Complex Embedding: exists digits of dvr
-- statement:
--   The Complex Embedding construction uses the exists digits of dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsComplexEmbeddingFractionFieldFiniteOverCdv.lean#L10-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsComplexEmbeddingFractionFieldFiniteOverCdv.lean#L10-L34

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

theorem GlobalTheory.ComplexEmbedding.exists_digits_of_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (ϖ : V) (hϖ : Irreducible ϖ) (s : ResidueField V → V) (hs : ∀ r, residue V (s r) = r) :
    ∀ (n : ℕ) (x : V), ∃ f : Fin n → ResidueField V,
      x - ∑ i : Fin n, s (f i) * ϖ ^ (i : ℕ) ∈ maximalIdeal V ^ n := by sorry
