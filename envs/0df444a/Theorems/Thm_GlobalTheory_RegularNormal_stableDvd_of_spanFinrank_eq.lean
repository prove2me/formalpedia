-- Prove2me | Theorems.Thm_GlobalTheory_RegularNormal_stableDvd_of_spanFinrank_eq
-- name    : GlobalTheory.RegularNormal.stableDvd_of_spanFinrank_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:20:08.304102+00:00
-- url     : https://prove2.me/theorems/704d2654-0ad2-4826-9073-aead6e53116d
-- title:
--   Regular Normal: stable Dvd of span Finrank eq
-- statement:
--   The Regular Normal construction uses the stable Dvd of span Finrank eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RegularLocalRingNormalDomain.lean#L109-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RegularLocalRingNormalDomain.lean#L109-L137

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSaturated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RegularLocalRingNormalDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
open GlobalTheory.RegularNormal
open ReciprocityTheory.CA.AB.RegA

theorem GlobalTheory.RegularNormal.stableDvd_of_spanFinrank_eq (n : ℕ) :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R],
      Submodule.spanFinrank (maximalIdeal R) = n → StableDvd R := by sorry
