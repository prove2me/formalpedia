-- Prove2me | Theorems.Thm_GlobalTheory_isRegular_ofFn_of_ringKrullDim_quotient_add_le
-- name    : GlobalTheory.isRegular_ofFn_of_ringKrullDim_quotient_add_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:01:41.92822+00:00
-- url     : https://prove2.me/theorems/9981ad13-c578-45fb-9a78-71a2829605c2
-- title:
--   Global Theory: is Regular of Fn of ring Krull Dim quotient add le
-- statement:
--   The Global Theory construction uses the is Regular of Fn of ring Krull Dim quotient add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsRegularOfFnOfRingKrullDimQuotientAddLe.lean#L6-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsRegularOfFnOfRingKrullDimQuotientAddLe.lean#L6-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsRegularOfFnOfRingKrullDimQuotientAddLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.isRegular_ofFn_of_ringKrullDim_quotient_add_le :
    ∀ (A : Type) [CommRing A] [IsRegularLocalRing A] (d r : ℕ) (f : Fin r → A),
      ringKrullDim A = d → (∀ i, f i ∈ IsLocalRing.maximalIdeal A) →
      ringKrullDim (A ⧸ Ideal.span (Set.range f)) + r ≤ d →
      RingTheory.Sequence.IsRegular A (List.ofFn f) := by sorry
