-- Prove2me | Theorems.Thm_GlobalTheory_RegularQuotient_exists_extend
-- name    : GlobalTheory.RegularQuotient.exists_extend
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:19:56.76829+00:00
-- url     : https://prove2.me/theorems/3dea2b56-fb2c-46b8-9ba1-f54395634113
-- title:
--   Regular Quotient: exists extend
-- statement:
--   The Regular Quotient construction uses the exists extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/QuotientSpanRange.lean#L72-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/QuotientSpanRange.lean#L72-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QuotientSpanRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Matrix
open GlobalTheory GlobalTheory.RegularQuotient
open IsLocalRing Matrix

theorem GlobalTheory.RegularQuotient.exists_extend (Λ : Type) [CommRing Λ]
    [IsRegularLocalRing Λ] {ι : Type} [Fintype ι]
    (τ : ι → maximalIdeal Λ)
    (hτ : LinearIndependent (ResidueField Λ) (fun i => (maximalIdeal Λ).toCotangent (τ i))) :
    ∃ (J : Type) (_ : Fintype J) (t : J → Λ),
      Ideal.span (Set.range t ∪ Set.range fun i => (τ i : Λ)) = maximalIdeal Λ ∧
      ringKrullDim Λ = ((Fintype.card J + Fintype.card ι : ℕ) : ℕ) := by sorry
