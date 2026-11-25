-- Prove2me | Theorems.Thm_GlobalTheory_exists_fixed_dvd_deg
-- name    : GlobalTheory.exists_fixed_dvd_deg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:19:47.656653+00:00
-- url     : https://prove2.me/theorems/69829c34-6610-57bd-82df-f1a40f3fbae0
-- title:
--   Global Theory: exists fixed dvd deg
-- statement:
--   The Global Theory construction uses the exists fixed dvd deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsRootOfUnityFixedDvdWeilGroupDegree.lean#L30-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsRootOfUnityFixedDvdWeilGroupDegree.lean#L30-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsRootOfUnityFixedDvdWeilGroupDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GlobalTheory
open NumberField IsDedekindDomain Polynomial

theorem GlobalTheory.exists_fixed_dvd_deg : ∀ (E Ω : Type) [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (k : ℕ), 0 < k →
    ∃ ζ : Ω, ∀ σ : _root_.GlobalTheory.WeilDeligne.Weil h, (σ : _root_.Formalism.ConjugateSelfDual.G E Ω) ζ = ζ → (k : ℤ) ∣ _root_.GlobalTheory.WeilDeligne.deg σ := by sorry
