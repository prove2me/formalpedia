-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_locIn_succ_nonunit_iff
-- name    : GlobalTheory.CMVal.Euler.locIn_succ_nonunit_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:04:54.628558+00:00
-- url     : https://prove2.me/theorems/6afa483b-e642-4dc0-b4e5-a24b3c492b46
-- title:
--   Euler: loc In succ nonunit iff
-- statement:
--   The Euler construction uses the loc In succ nonunit iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUniformiserSplitPlaceCmOrderNonunit.lean#L33-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUniformiserSplitPlaceCmOrderNonunit.lean#L33-L92

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

theorem GlobalTheory.CMVal.Euler.locIn_succ_nonunit_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (OF E)), Splits v → ∃ x : OF E, (∀ P, Over P v → Valued.v (iota x P) = WithZero.exp (-1 : ℤ)) ∧ ∀ (n : ℕ) (π y : (Af E)ˣ), (∀ P, Over P v → (π : Af E) P = iota x P) → (LocIn n v ((π⁻¹ * y : (Af E)ˣ) : Af E) ↔ LocIn (n + 1) v (y : Af E) ∧ ¬ ∀ P, Over P v → Valued.v ((y : Af E) P) = 1) := by sorry
