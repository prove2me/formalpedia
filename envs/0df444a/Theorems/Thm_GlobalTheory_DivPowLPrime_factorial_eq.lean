-- Prove2me | Theorems.Thm_GlobalTheory_DivPowLPrime_factorial_eq
-- name    : GlobalTheory.DivPowLPrime.factorial_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:50:22.916257+00:00
-- url     : https://prove2.me/theorems/55d26617-c971-44bd-a5b3-3718750e7143
-- title:
--   Div Pow LPrime: factorial eq
-- statement:
--   The Div Pow LPrime construction uses the factorial eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DividedPowersPrimeUnique.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DividedPowersPrimeUnique.lean#L35-L38

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

theorem GlobalTheory.DivPowLPrime.factorial_eq {l : ℕ} (hl : l.Prime) (m : ℕ) :
    m.factorial = l ^ padicValNat l m.factorial * factPrimePart l m := by sorry
