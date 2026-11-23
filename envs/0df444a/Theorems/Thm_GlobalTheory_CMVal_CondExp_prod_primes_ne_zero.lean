-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_CondExp_prod_primes_ne_zero
-- name    : GlobalTheory.CMVal.CondExp.prod_primes_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:52.691599+00:00
-- url     : https://prove2.me/theorems/1ccea2f2-ec8c-407a-9344-0b1f5f713651
-- title:
--   Cond Exp: prod primes ne zero
-- statement:
--   The Cond Exp construction uses the prod primes ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConductorTimesSplitPrimesExponents.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConductorTimesSplitPrimesExponents.lean#L21-L23

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

theorem GlobalTheory.CMVal.CondExp.prod_primes_ne_zero {R : Type} [CommRing R] [IsDedekindDomain R]
    (Q : Finset (HeightOneSpectrum R)) : ∏ q ∈ Q, q.asIdeal ≠ 0 := by sorry
