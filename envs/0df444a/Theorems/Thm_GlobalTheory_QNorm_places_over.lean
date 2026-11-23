-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_places_over
-- name    : GlobalTheory.QNorm.places_over
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:15:43.502875+00:00
-- url     : https://prove2.me/theorems/51b95f9d-5957-4681-825f-007f122b41b4
-- title:
--   QNorm: places over
-- statement:
--   The QNorm construction uses the places over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/HeightOneSpectrumPlacesOverFiniteSet.lean#L23-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/HeightOneSpectrumPlacesOverFiniteSet.lean#L23-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HeightOneSpectrumPlacesOverFiniteSet
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
open GlobalTheory GlobalTheory.QNorm
open NumberField IsDedekindDomain
open scoped WithZero

theorem GlobalTheory.QNorm.places_over : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ SE : Finset (HeightOneSpectrum (𝓞 E)), ∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) ∧ (∀ v : HeightOneSpectrum (𝓞 F), ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v) ∧ ∀ (w : HeightOneSpectrum (𝓞 E)), ∃ e : ℕ, 0 < e ∧ ∀ x : F, w.valuation E (algebraMap F E x) = (w.under (𝓞 F)).valuation F x ^ e := by sorry
