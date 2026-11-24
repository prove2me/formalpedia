-- Prove2me | Theorems.Thm_GlobalTheory_HeckeSplit_finite_setOf_mem_asIdeal
-- name    : GlobalTheory.HeckeSplit.finite_setOf_mem_asIdeal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:04:53.478913+00:00
-- url     : https://prove2.me/theorems/a7c1b5e4-fac9-4e65-88f4-20f676fd2222
-- title:
--   Hecke Split: finite set Of mem as Ideal
-- statement:
--   The Hecke Split construction uses the finite set Of mem as Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EventuallyResidueDegreeOnePrimeMovedByGalois.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EventuallyResidueDegreeOnePrimeMovedByGalois.lean#L17-L22

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

theorem GlobalTheory.HeckeSplit.finite_setOf_mem_asIdeal (E : Type) [Field E] [NumberField E] (δ : 𝓞 E) (h : δ ≠ 0) :
    {w : HeightOneSpectrum (𝓞 E) | δ ∈ w.asIdeal}.Finite := by sorry
