-- Prove2me | Theorems.Thm_GlobalTheory_RegularAscent_spanFinrank_maximalIdeal_le
-- name    : GlobalTheory.RegularAscent.spanFinrank_maximalIdeal_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:19:22.455798+00:00
-- url     : https://prove2.me/theorems/e22dd00a-d224-48dc-8665-67db942b1407
-- title:
--   Regular Ascent: span Finrank maximal Ideal le
-- statement:
--   The Regular Ascent construction uses the span Finrank maximal Ideal le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRegularLocalRingOfRegularQuotient.lean#L23-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRegularLocalRingOfRegularQuotient.lean#L23-L50

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

theorem GlobalTheory.RegularAscent.spanFinrank_maximalIdeal_le {R : Type} [CommRing R] [IsLocalRing R] (p : Ideal R)
    [p.IsPrime] [IsLocalRing (R ⧸ p)] (r : ℕ) (f : Fin r → R) (hf : p = Ideal.span (Set.range f))
    (hfg : (maximalIdeal (R ⧸ p)).FG) :
    (maximalIdeal R).spanFinrank ≤ r + (maximalIdeal (R ⧸ p)).spanFinrank := by sorry
