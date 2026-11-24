-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AePoly_measurePreserving_uncurry
-- name    : GlobalTheory.CompanionTheory.AePoly.measurePreserving_uncurry
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:16:33.330346+00:00
-- url     : https://prove2.me/theorems/f1ae738d-595b-4196-9728-424782cb3b66
-- title:
--   Ae Poly: measure Preserving uncurry
-- statement:
--   The Ae Poly construction uses the measure Preserving uncurry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AePolynomialNonvanishing.lean#L60-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AePolynomialNonvanishing.lean#L60-L73

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AePolynomialNonvanishing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AePoly

theorem GlobalTheory.CompanionTheory.AePoly.measurePreserving_uncurry (M n : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin M) (Fin n) ℂ).symm
      (volume : Measure (Fin M → Fin n → ℂ)) (volume : Measure (Fin M × Fin n → ℂ)) := by sorry
