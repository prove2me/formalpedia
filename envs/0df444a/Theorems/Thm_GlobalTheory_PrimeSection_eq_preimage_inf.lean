-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_eq_preimage_inf
-- name    : GlobalTheory.PrimeSection.eq_preimage_inf
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:42:42.659646+00:00
-- url     : https://prove2.me/theorems/fe5f171c-cb9a-4f30-a541-d7d9146fb1a4
-- title:
--   Prime Section: eq preimage inf
-- statement:
--   The Prime Section construction uses the eq preimage inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueZpowMulAppLE.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueZpowMulAppLE.lean#L38-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection

theorem GlobalTheory.PrimeSection.eq_preimage_inf {X Y : Scheme.{u}} {j : Y ⟶ X} [IsOpenImmersion j] {D U : X.Opens}
    (hj : j.opensRange = D) {W : Y.Opens} (h : W = j ⁻¹ᵁ U) : W = j ⁻¹ᵁ (U ⊓ D) := by sorry
