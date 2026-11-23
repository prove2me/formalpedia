-- Prove2me | Theorems.Thm_GlobalTheory_PrimeElement_isPrime_span
-- name    : GlobalTheory.PrimeElement.isPrime_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:36.319638+00:00
-- url     : https://prove2.me/theorems/14614415-6c72-4caa-9d17-c1992d624d4a
-- title:
--   Prime Element: is Prime span
-- statement:
--   The Prime Element construction uses the is Prime span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUnitAlgebraMapEqOfValuationEqOne.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUnitAlgebraMapEqOfValuationEqOne.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PrimeElement
variable {R : Type*} [CommRing R] {π : R}

theorem GlobalTheory.PrimeElement.isPrime_span (hπ : Prime π) : (Ideal.span {π}).IsPrime := by sorry
