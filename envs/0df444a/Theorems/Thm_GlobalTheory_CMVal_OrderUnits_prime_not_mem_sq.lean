-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_OrderUnits_prime_not_mem_sq
-- name    : GlobalTheory.CMVal.OrderUnits.prime_not_mem_sq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:05:15.528354+00:00
-- url     : https://prove2.me/theorems/6aabe7c9-e099-4222-95f3-70a4793e6ed0
-- title:
--   Order Units: prime not mem sq
-- statement:
--   The Order Units construction uses the prime not mem sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmRingClassOrderUnitsEqMaxRealSubfieldUnits.lean#L9-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmRingClassOrderUnitsEqMaxRealSubfieldUnits.lean#L9-L37

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmRingClassOrderUnitsEqMaxRealSubfieldUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.OrderUnits

theorem GlobalTheory.CMVal.OrderUnits.prime_not_mem_sq {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E)
    (w : HeightOneSpectrum (𝓞 E)) (hv : (p : 𝓞 E) ∈ w.asIdeal) : (p : 𝓞 E) ∉ w.asIdeal ^ 2 := by sorry
