-- Prove2me | Theorems.Thm_GlobalTheory_DivPowLPrime_qCoef_eq_mul
-- name    : GlobalTheory.DivPowLPrime.qCoef_eq_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:50:12.493153+00:00
-- url     : https://prove2.me/theorems/d43d9b1f-7568-4d8a-96f8-fca626da60c8
-- title:
--   Div Pow LPrime: q Coef eq mul
-- statement:
--   The Div Pow LPrime construction uses the q Coef eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DividedPowersPrimeUnique.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DividedPowersPrimeUnique.lean#L62-L64

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

theorem GlobalTheory.DivPowLPrime.qCoef_eq_mul {m : ℕ} (h : lPrimeExp l ≤ qExp l m) :
    qCoef O l m = (lPrime l : O) * ((l : O) ^ (qExp l m - lPrimeExp l) * Ring.inverse (factPrimePart l m : O)) := by sorry
