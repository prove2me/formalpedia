-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_CondExp_multiplicity_prod_primes_of_mem
-- name    : GlobalTheory.CMVal.CondExp.multiplicity_prod_primes_of_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:05:39.846951+00:00
-- url     : https://prove2.me/theorems/5b44e8bd-d85f-464c-8867-b3014d375447
-- title:
--   Cond Exp: multiplicity prod primes of mem
-- statement:
--   The Cond Exp construction uses the multiplicity prod primes of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConductorTimesSplitPrimesExponents.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConductorTimesSplitPrimesExponents.lean#L25-L32

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConductorTimesSplitPrimesExponents
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.CondExp

theorem GlobalTheory.CMVal.CondExp.multiplicity_prod_primes_of_mem {R : Type} [CommRing R] [IsDedekindDomain R]
    (Q : Finset (HeightOneSpectrum R)) (v : HeightOneSpectrum R) (hv : v ∈ Q) :
    multiplicity v.asIdeal (∏ q ∈ Q, q.asIdeal) = 1 := by sorry
