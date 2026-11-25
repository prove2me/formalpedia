-- Prove2me | Theorems.Thm_GlobalTheory_exists_normalisation_adjoin_finset_dvr
-- name    : GlobalTheory.exists_normalisation_adjoin_finset_dvr
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:05:54.676962+00:00
-- url     : https://prove2.me/theorems/9baee433-71da-470c-9de9-b910f3ef21ed
-- title:
--   Global Theory: exists normalisation adjoin finset dvr
-- statement:
--   The Global Theory construction uses the exists normalisation adjoin finset dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IsFractionRingSubringOfClosureEqTop.lean#L26-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IsFractionRingSubringOfClosureEqTop.lean#L26-L102

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsFractionRingSubringOfClosureEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_normalisation_adjoin_finset_dvr :
    ∀ (O Ω : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Field Ω] [Algebra O Ω], Function.Injective (algebraMap O Ω) → ∀ (s : Finset Ω), Subfield.closure (Set.range (algebraMap O Ω) ∪ (s : Set Ω)) = ⊤ → ∃ A : Subalgebra O Ω, (s : Set Ω) ⊆ A ∧ Algebra.FiniteType O A ∧ Module.Flat O A ∧ IsIntegrallyClosed A ∧ IsFractionRing A Ω ∧ (∀ D : Subring Ω, IsIntegrallyClosed D → (∀ a, algebraMap O Ω a ∈ D) → (s : Set Ω) ⊆ D → (A : Set Ω) ⊆ D) ∧ ∀ (L : Type) [Field L] (W : ValuationSubring L) (φ : A →+* L), (∀ a, φ (algebraMap O A a) ∈ W) → (∀ (x : A), (x : Ω) ∈ s → φ x ∈ W) → ∀ x, φ x ∈ W := by sorry
