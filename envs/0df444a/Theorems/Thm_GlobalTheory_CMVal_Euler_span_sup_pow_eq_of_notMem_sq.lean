-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_span_sup_pow_eq_of_notMem_sq
-- name    : GlobalTheory.CMVal.Euler.span_sup_pow_eq_of_notMem_sq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:05:30.08188+00:00
-- url     : https://prove2.me/theorems/432cde34-b70a-4e05-900b-c9ca8f3de95f
-- title:
--   Euler: span sup pow eq of not Mem sq
-- statement:
--   The Euler construction uses the span sup pow eq of not Mem sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUniformiserSplitPlaceCmOrderNonunit.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUniformiserSplitPlaceCmOrderNonunit.lean#L11-L23

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitsInCMFieldTwoPrimesDegreeOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniformiserSplitPlaceCmOrderNonunit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler

theorem GlobalTheory.CMVal.Euler.span_sup_pow_eq_of_notMem_sq {R : Type} [CommRing R] [IsDedekindDomain R] (v : HeightOneSpectrum R) {x : R}
    (hx : x ∈ v.asIdeal) (hx2 : x ∉ v.asIdeal ^ 2) (n : ℕ) : Ideal.span {x} ⊔ v.asIdeal ^ (n + 1) = v.asIdeal := by sorry
