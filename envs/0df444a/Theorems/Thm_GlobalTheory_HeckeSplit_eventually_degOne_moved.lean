-- Prove2me | Theorems.Thm_GlobalTheory_HeckeSplit_eventually_degOne_moved
-- name    : GlobalTheory.HeckeSplit.eventually_degOne_moved
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:04:33.610819+00:00
-- url     : https://prove2.me/theorems/c482c5f1-c2d5-4497-a35c-b37922cc2d16
-- title:
--   Hecke Split: eventually deg One moved
-- statement:
--   The Hecke Split construction uses the eventually deg One moved property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EventuallyResidueDegreeOnePrimeMovedByGalois.lean#L24-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EventuallyResidueDegreeOnePrimeMovedByGalois.lean#L24-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_DegOneIffSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EventuallyResidueDegreeOnePrimeMovedByGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit
open GlobalTheory GlobalTheory.HeckeSplit

theorem GlobalTheory.HeckeSplit.eventually_degOne_moved : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [Algebra.IsQuadraticExtension F E] (c : E ≃ₐ[F] E), c ≠ 1 →
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, DegOne F w →
      ∃ x : 𝓞 E, x ∈ w.asIdeal ∧ ∀ y : 𝓞 E, (y : E) = c (x : E) → y ∉ w.asIdeal := by sorry
