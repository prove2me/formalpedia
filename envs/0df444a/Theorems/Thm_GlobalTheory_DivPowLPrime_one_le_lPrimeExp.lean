-- Prove2me | Theorems.Thm_GlobalTheory_DivPowLPrime_one_le_lPrimeExp
-- name    : GlobalTheory.DivPowLPrime.one_le_lPrimeExp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:50:45.759878+00:00
-- url     : https://prove2.me/theorems/6938cf76-afb7-46c5-9891-3f7bd529ec6d
-- title:
--   Div Pow LPrime: one le l Prime Exp
-- statement:
--   The Div Pow LPrime construction uses the one le l Prime Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DividedPowersPrimeUnique.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DividedPowersPrimeUnique.lean#L13-L14

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

theorem GlobalTheory.DivPowLPrime.one_le_lPrimeExp (l : ℕ) : 1 ≤ lPrimeExp l := by sorry
