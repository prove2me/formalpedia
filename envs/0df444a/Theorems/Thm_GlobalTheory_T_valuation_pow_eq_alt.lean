-- Prove2me | Theorems.Thm_GlobalTheory_T_valuation_pow_eq_alt
-- name    : GlobalTheory.T.valuation_pow_eq_alt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:01:15.430026+00:00
-- url     : https://prove2.me/theorems/cb228d7f-cabf-430f-be4b-fedc970bdbf5
-- title:
--   T: valuation pow eq alt
-- statement:
--   The T construction uses the valuation pow eq alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValVpNatCastPowStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValVpNatCastPowStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValVpNatCastPow
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValVpNatCastPowStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.valuation_pow_eq_alt : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], ∀ (l : ℕ), l ≠ 0 → (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ k : ℕ, val_vp O l (algebraMap O K ((l : O) ^ k)) = ((k : ℚ) : WithTop ℚ) := by sorry
