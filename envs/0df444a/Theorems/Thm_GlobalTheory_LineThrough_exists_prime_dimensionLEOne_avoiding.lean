-- Prove2me | Theorems.Thm_GlobalTheory_LineThrough_exists_prime_dimensionLEOne_avoiding
-- name    : GlobalTheory.LineThrough.exists_prime_dimensionLEOne_avoiding
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:13:42.887562+00:00
-- url     : https://prove2.me/theorems/33d526af-50cd-4468-a752-69939aea03bb
-- title:
--   Line Through: exists prime dimension LEOne avoiding
-- statement:
--   The Line Through construction uses the exists prime dimension LEOne avoiding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsPrimeDimensionLEOneAvoiding.lean#L90-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsPrimeDimensionLEOneAvoiding.lean#L90-L149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsPrimeDimensionLEOneAvoiding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.LineThrough

theorem GlobalTheory.LineThrough.exists_prime_dimensionLEOne_avoiding
    (E : Type) [CommRing E] [IsDomain E] [Algebra ℂ E] [Algebra.FiniteType ℂ E]
    (e : E →ₐ[ℂ] ℂ) (T : Set E) (hT : T.Countable) (h0 : (0 : E) ∉ T) :
    ∃ Q : Ideal E, Q.IsPrime ∧ Q ≤ RingHom.ker e ∧ (∀ r ∈ T, r ∉ Q) ∧
      Ring.DimensionLEOne (E ⧸ Q) := by sorry
