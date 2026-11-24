-- Prove2me | Theorems.Thm_GlobalTheory_exists_finite_intermediateField_range_le
-- name    : GlobalTheory.exists_finite_intermediateField_range_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:31:48.980432+00:00
-- url     : https://prove2.me/theorems/6c216ead-7bc5-476d-b0c5-9577782f474a
-- title:
--   Global Theory: exists finite intermediate Field range le
-- statement:
--   The Global Theory construction uses the exists finite intermediate Field range le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsContinuousExtensionAdicCompletion.lean#L7-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsContinuousExtensionAdicCompletion.lean#L7-L20

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsContinuousExtensionAdicCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory

theorem GlobalTheory.exists_finite_intermediateField_range_le (E : Type) [Field E] [NumberField E] (l : ℕ)
    [Fact l.Prime] (τ : E →+* PadicAlgCl l) :
    ∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧ ∀ x, τ x ∈ K := by sorry
