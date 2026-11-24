-- Prove2me | Theorems.Thm_GlobalTheory_T_eventually_residueDegreeOne_prime_moved_by_galois
-- name    : GlobalTheory.T.eventually_residueDegreeOne_prime_moved_by_galois
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:33:20.014653+00:00
-- url     : https://prove2.me/theorems/482b3579-2f95-41d6-9773-39c4686a685f
-- title:
--   T: eventually residue Degree One prime moved by galois
-- statement:
--   The T construction uses the eventually residue Degree One prime moved by galois property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EventuallyResidueDegreeOnePrimeMovedByGaloisStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EventuallyResidueDegreeOnePrimeMovedByGaloisStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EventuallyResidueDegreeOnePrimeMovedByGalois
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_DegOneIffSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EventuallyResidueDegreeOnePrimeMovedByGaloisStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.eventually_residueDegreeOne_prime_moved_by_galois : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E] (c : E ≃ₐ[F] E), c ≠ 1 → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, DegOne F w → ∃ x : 𝓞 E, x ∈ w.asIdeal ∧ ∀ y : 𝓞 E, (y : E) = c (x : E) → y ∉ w.asIdeal := by sorry
