-- Prove2me | Theorems.Thm_GlobalTheory_HeckeSplit_exists_int_moved
-- name    : GlobalTheory.HeckeSplit.exists_int_moved
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:04:59.24768+00:00
-- url     : https://prove2.me/theorems/b128f375-5538-4f8b-861b-22cedc75afd7
-- title:
--   Hecke Split: exists int moved
-- statement:
--   The Hecke Split construction uses the exists int moved property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EventuallyResidueDegreeOnePrimeMovedByGalois.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EventuallyResidueDegreeOnePrimeMovedByGalois.lean#L7-L15

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

theorem GlobalTheory.HeckeSplit.exists_int_moved (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (c : E ≃ₐ[F] E) (hc : c ≠ 1) : ∃ θ : 𝓞 E, c (θ : E) ≠ (θ : E) := by sorry
