-- Prove2me | Theorems.Thm_GlobalTheory_RegularAscent_height_add_ringKrullDim_quotient_le
-- name    : GlobalTheory.RegularAscent.height_add_ringKrullDim_quotient_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:19:34.894706+00:00
-- url     : https://prove2.me/theorems/b6ca751f-474f-4839-934f-262bf00c817a
-- title:
--   Regular Ascent: height add ring Krull Dim quotient le
-- statement:
--   The Regular Ascent construction uses the height add ring Krull Dim quotient le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRegularLocalRingOfRegularQuotient.lean#L7-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRegularLocalRingOfRegularQuotient.lean#L7-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRegularLocalRingOfRegularQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.RegularAscent

theorem GlobalTheory.RegularAscent.height_add_ringKrullDim_quotient_le {R : Type} [CommRing R] (p : Ideal R) [hp : p.IsPrime] :
    ((p.height : ℕ∞) : WithBot ℕ∞) + ringKrullDim (R ⧸ p) ≤ ringKrullDim R := by sorry
