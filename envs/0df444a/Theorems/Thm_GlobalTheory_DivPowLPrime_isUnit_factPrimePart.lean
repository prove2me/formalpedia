-- Prove2me | Theorems.Thm_GlobalTheory_DivPowLPrime_isUnit_factPrimePart
-- name    : GlobalTheory.DivPowLPrime.isUnit_factPrimePart
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:50:28.204531+00:00
-- url     : https://prove2.me/theorems/4df93cac-e2fb-4607-93e6-70f59225cc75
-- title:
--   Div Pow LPrime: is Unit fact Prime Part
-- statement:
--   The Div Pow LPrime construction uses the is Unit fact Prime Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DividedPowersPrimeUnique.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DividedPowersPrimeUnique.lean#L44-L46

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

theorem GlobalTheory.DivPowLPrime.isUnit_factPrimePart (hl : l.Prime) (hlO : (l : O) ∈ IsLocalRing.maximalIdeal O) (m : ℕ) :
    IsUnit (factPrimePart l m : O) := by sorry
