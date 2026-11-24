-- Prove2me | Theorems.Thm_GlobalTheory_FinPlaceApprox_exists_approx_finite_places
-- name    : GlobalTheory.FinPlaceApprox.exists_approx_finite_places
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:24:50.571572+00:00
-- url     : https://prove2.me/theorems/885ff2e6-2add-4af8-9ebb-3479dd612b52
-- title:
--   Fin Place Approx: exists approx finite places
-- statement:
--   The Fin Place Approx construction uses the exists approx finite places property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsApproxFinitePlacesNumberFieldTarget.lean#L10-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsApproxFinitePlacesNumberFieldTarget.lean#L10-L41

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsApproxFinitePlacesNumberFieldTarget
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
noncomputable section
open GlobalTheory GlobalTheory.FinPlaceApprox

theorem GlobalTheory.FinPlaceApprox.exists_approx_finite_places (F : Type) [Field F] [NumberField F]
    (T : Finset (HeightOneSpectrum (𝓞 F))) (t : HeightOneSpectrum (𝓞 F) → F) (M : ℕ) :
    ∃ a : F, ∀ v ∈ T, v.valuation F (a - t v) ≤ WithZero.exp (-(M : ℤ)) := by sorry
