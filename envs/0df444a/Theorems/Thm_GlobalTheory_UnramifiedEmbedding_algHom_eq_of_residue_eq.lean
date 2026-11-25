-- Prove2me | Theorems.Thm_GlobalTheory_UnramifiedEmbedding_algHom_eq_of_residue_eq
-- name    : GlobalTheory.UnramifiedEmbedding.algHom_eq_of_residue_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:58:07.613866+00:00
-- url     : https://prove2.me/theorems/ae5b1db3-ec4b-5821-b83a-43b510143f44
-- title:
--   Unramified Embedding: alg Hom eq of residue eq
-- statement:
--   The Unramified Embedding construction uses the alg Hom eq of residue eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RangeLeRangeOfIsUnramifiedAt.lean#L9-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RangeLeRangeOfIsUnramifiedAt.lean#L9-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GaloisOfPrimePowerDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RangeLeRangeOfIsUnramifiedAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IsLocalRing NumberField
open GlobalTheory GlobalTheory.UnramifiedEmbedding

theorem GlobalTheory.UnramifiedEmbedding.algHom_eq_of_residue_eq {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [IsLocalRing T] [Algebra R S] [Algebra R T] [Algebra.IsStandardEtale R S] {χ₁ χ₂ : S →ₐ[R] T}
    (h : ∀ s, residue T (χ₁ s) = residue T (χ₂ s)) : χ₁ = χ₂ := by sorry
