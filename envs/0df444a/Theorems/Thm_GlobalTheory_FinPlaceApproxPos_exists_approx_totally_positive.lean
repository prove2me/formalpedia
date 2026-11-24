-- Prove2me | Theorems.Thm_GlobalTheory_FinPlaceApproxPos_exists_approx_totally_positive
-- name    : GlobalTheory.FinPlaceApproxPos.exists_approx_totally_positive
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:24:52.115647+00:00
-- url     : https://prove2.me/theorems/a70e1939-6c13-4479-b914-0bcc2be6a645
-- title:
--   Fin Place Approx Pos: exists approx totally positive
-- statement:
--   The Fin Place Approx Pos construction uses the exists approx totally positive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTotallyPositiveApproxAtFinitePlaces.lean#L11-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTotallyPositiveApproxAtFinitePlaces.lean#L11-L55

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsApproxFinitePlacesNumberFieldTarget
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTotallyPositiveApproxAtFinitePlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.FinPlaceApproxPos

theorem GlobalTheory.FinPlaceApproxPos.exists_approx_totally_positive (F : Type) [Field F] [NumberField F]
    (T : Finset (HeightOneSpectrum (𝓞 F))) (t : HeightOneSpectrum (𝓞 F) → F) (M : ℕ) :
    ∃ a : F, (∀ v ∈ T, v.valuation F (a - t v) ≤ WithZero.exp (-(M : ℤ))) ∧
      ∀ φ : F →+* ℝ, 0 < φ a := by sorry
