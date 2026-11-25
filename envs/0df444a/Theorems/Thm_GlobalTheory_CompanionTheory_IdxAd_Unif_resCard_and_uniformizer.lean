-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IdxAd_Unif_resCard_and_uniformizer
-- name    : GlobalTheory.CompanionTheory.IdxAd.Unif.resCard_and_uniformizer
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:02:19.524227+00:00
-- url     : https://prove2.me/theorems/91c01701-5664-4eda-beac-f9161bc266bb
-- title:
--   Unif: res Card and uniformizer
-- statement:
--   The Unif construction uses the res Card and uniformizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ResCardAndUniformizer.lean#L9-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ResCardAndUniformizer.lean#L9-L41

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SwapCApply
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ResCardAndUniformizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain GlobalTheory.CompanionTheory.IdxAd
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IdxAd GlobalTheory.CompanionTheory.IdxAd.Unif

theorem GlobalTheory.CompanionTheory.IdxAd.Unif.resCard_and_uniformizer : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), GlobalTheory.SplitWeil.resCard (v.adicCompletion F) = Ideal.absNorm v.asIdeal ∧ ∃ ϖ : (v.adicCompletion F)ˣ, (∃ p : 𝒪[v.adicCompletion F], Irreducible p ∧ (p : v.adicCompletion F) = ϖ) ∧ ∀ t : (v.adicCompletion F)ˣ, ∃ (a : ℤ) (u : (v.adicCompletion F)ˣ), (u : v.adicCompletion F) ∈ 𝒪[v.adicCompletion F] ∧ ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ 𝒪[v.adicCompletion F] ∧ t = u * ϖ ^ a ∧ a.natAbs = (WithZero.log (Valued.v (t : v.adicCompletion F))).natAbs := by sorry
