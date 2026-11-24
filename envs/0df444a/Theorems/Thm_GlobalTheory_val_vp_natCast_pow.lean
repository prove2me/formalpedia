-- Prove2me | Theorems.Thm_GlobalTheory_val_vp_natCast_pow
-- name    : GlobalTheory.val_vp_natCast_pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:24:52.346924+00:00
-- url     : https://prove2.me/theorems/cb378793-2e0c-456a-8177-1eb97f943a45
-- title:
--   Global Theory: val vp nat Cast pow
-- statement:
--   The Global Theory construction uses the val vp nat Cast pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValVpNatCastPow.lean#L8-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValVpNatCastPow.lean#L8-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValVpNatCastPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory

theorem GlobalTheory.val_vp_natCast_pow (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K]
    [Algebra O K] [IsFractionRing O K] (l : ℕ) (hl : l ≠ 0) (h : (l : O) ∈ IsLocalRing.maximalIdeal O) (k : ℕ) :
    val_vp O l (algebraMap O K ((l : O) ^ k)) = ((k : ℚ) : WithTop ℚ) := by sorry
