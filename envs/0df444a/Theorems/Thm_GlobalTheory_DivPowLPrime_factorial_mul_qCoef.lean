-- Prove2me | Theorems.Thm_GlobalTheory_DivPowLPrime_factorial_mul_qCoef
-- name    : GlobalTheory.DivPowLPrime.factorial_mul_qCoef
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:50:30.284578+00:00
-- url     : https://prove2.me/theorems/3044aec8-1663-413d-a314-fc883b1d9a6b
-- title:
--   Div Pow LPrime: factorial mul q Coef
-- statement:
--   The Div Pow LPrime construction uses the factorial mul q Coef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DividedPowersPrimeUnique.lean#L48-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DividedPowersPrimeUnique.lean#L48-L60

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
variable {O : Type} [CommRing O] [IsLocalRing O] {l : ℕ}

theorem GlobalTheory.DivPowLPrime.factorial_mul_qCoef (hl : l.Prime) (hlO : (l : O) ∈ IsLocalRing.maximalIdeal O) (m : ℕ)
    (hv : padicValNat l m.factorial ≤ lPrimeExp l * m) :
    (m.factorial : O) * qCoef O l m = (lPrime l : O) ^ m := by sorry
