-- Prove2me | Theorems.Thm_GlobalTheory_T_heightOneSpectrum_places_over_finite_set
-- name    : GlobalTheory.T.heightOneSpectrum_places_over_finite_set
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:45:55.936805+00:00
-- url     : https://prove2.me/theorems/9f57b746-dcbf-4b9f-b359-40f76fed36d4
-- title:
--   T: height One Spectrum places over finite set
-- statement:
--   The T construction uses the height One Spectrum places over finite set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/HeightOneSpectrumPlacesOverFiniteSetStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/HeightOneSpectrumPlacesOverFiniteSetStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HeightOneSpectrumPlacesOverFiniteSet
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HeightOneSpectrumPlacesOverFiniteSetStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.heightOneSpectrum_places_over_finite_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ SE : Finset (HeightOneSpectrum (𝓞 E)), ∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) ∧ (∀ v : HeightOneSpectrum (𝓞 F), ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v) ∧ ∀ (w : HeightOneSpectrum (𝓞 E)), ∃ e : ℕ, 0 < e ∧ ∀ x : F, w.valuation E (algebraMap F E x) = (w.under (𝓞 F)).valuation F x ^ e := by sorry
