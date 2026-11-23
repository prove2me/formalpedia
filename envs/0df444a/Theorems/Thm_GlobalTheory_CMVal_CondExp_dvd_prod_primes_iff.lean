-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_CondExp_dvd_prod_primes_iff
-- name    : GlobalTheory.CMVal.CondExp.dvd_prod_primes_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:46.799116+00:00
-- url     : https://prove2.me/theorems/5b0abe3b-ca1c-45de-b7fd-a3a985b1d11a
-- title:
--   Cond Exp: dvd prod primes iff
-- statement:
--   The Cond Exp construction uses the dvd prod primes iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConductorTimesSplitPrimesExponents.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConductorTimesSplitPrimesExponents.lean#L9-L19

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

theorem GlobalTheory.CMVal.CondExp.dvd_prod_primes_iff {R : Type} [CommRing R] [IsDedekindDomain R]
    (Q : Finset (HeightOneSpectrum R)) (v : HeightOneSpectrum R) :
    v.asIdeal ∣ ∏ q ∈ Q, q.asIdeal ↔ v ∈ Q := by sorry
