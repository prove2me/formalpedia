-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CosetSum_integrable_iff_and_integral_eq
-- name    : GlobalTheory.CompanionTheory.CosetSum.integrable_iff_and_integral_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:00:46.683221+00:00
-- url     : https://prove2.me/theorems/57335559-00af-4c64-9ebe-3fc535fbdec7
-- title:
--   Coset Sum: integrable iff and integral eq
-- statement:
--   The Coset Sum construction uses the integrable iff and integral eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetIntegralUnramified.lean#L39-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetIntegralUnramified.lean#L39-L83

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetIntegralUnramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CosetSum
variable {G : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]

theorem GlobalTheory.CompanionTheory.CosetSum.integrable_iff_and_integral_eq (G : Type) [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd G] (ν : Measure G) [ν.IsAddLeftInvariant] (H : AddSubgroup G)
    (hm : ∀ g : G, MeasurableSet {x | x - g ∈ H}) (h1 : ν (H : Set G) = 1)
    (hc : Countable (G ⧸ H)) (f : G → ℂ) (fbar : G ⧸ H → ℂ)
    (hf : ∀ g : G, f g = fbar (g : G ⧸ H)) :
    (Integrable f ν ↔ Summable fun c => ‖fbar c‖) ∧
      ((Summable fun c => ‖fbar c‖) → ∫ g, f g ∂ν = ∑' c, fbar c) := by sorry
