-- Prove2me | Theorems.Thm_GlobalTheory_T_splitsInCMField_two_primes_degree_one
-- name    : GlobalTheory.T.splitsInCMField_two_primes_degree_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:10:00.533036+00:00
-- url     : https://prove2.me/theorems/57937eee-d0ee-4a20-b16e-962a4fda861d
-- title:
--   T: splits In CMField two primes degree one
-- statement:
--   The T construction uses the splits In CMField two primes degree one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplitsInCMFieldTwoPrimesDegreeOneStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplitsInCMFieldTwoPrimesDegreeOneStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitsInCMFieldTwoPrimesDegreeOne
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitsInCMFieldTwoPrimesDegreeOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.splitsInCMField_two_primes_degree_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (OF E)), Splits v → (∀ P P' : HeightOneSpectrum (𝓞 E), Over P v → Over P' v → P ≠ P' → ∀ R : HeightOneSpectrum (𝓞 E), Over R v → R = P ∨ R = P') ∧ ∀ P : HeightOneSpectrum (𝓞 E), Over P v → Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ (∀ (a : OF E) (k : ℕ), algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal ^ k ↔ a ∈ v.asIdeal ^ k) ∧ ∀ b : 𝓞 E, ∃ a : OF E, b - algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal := by sorry
