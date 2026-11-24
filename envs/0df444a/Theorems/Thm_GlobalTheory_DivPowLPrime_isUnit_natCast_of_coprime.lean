-- Prove2me | Theorems.Thm_GlobalTheory_DivPowLPrime_isUnit_natCast_of_coprime
-- name    : GlobalTheory.DivPowLPrime.isUnit_natCast_of_coprime
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:50:19.72391+00:00
-- url     : https://prove2.me/theorems/5f091a00-67da-4126-9262-551d05a060a1
-- title:
--   Div Pow LPrime: is Unit nat Cast of coprime
-- statement:
--   The Div Pow LPrime construction uses the is Unit nat Cast of coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DividedPowersPrimeUnique.lean#L16-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DividedPowersPrimeUnique.lean#L16-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DividedPowersPrimeUnique
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
noncomputable section
open GlobalTheory GlobalTheory.DivPowLPrime

theorem GlobalTheory.DivPowLPrime.isUnit_natCast_of_coprime {O : Type} [CommRing O] [IsLocalRing O] {l c : ℕ}
    (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hc : Nat.Coprime l c) : IsUnit (c : O) := by sorry
