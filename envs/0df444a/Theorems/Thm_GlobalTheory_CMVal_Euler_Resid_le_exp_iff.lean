-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_Resid_le_exp_iff
-- name    : GlobalTheory.CMVal.Euler.Resid.le_exp_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:37.964329+00:00
-- url     : https://prove2.me/theorems/3bba439c-7ac0-4018-adaa-470a8d796f01
-- title:
--   Resid: le exp iff
-- statement:
--   The Resid construction uses the le exp iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLocalUnitRepresentativesSplitPrime.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLocalUnitRepresentativesSplitPrime.lean#L16-L20

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitsInCMFieldTwoPrimesDegreeOne
import Definitions.Def_ReciprocityTheory_Automorphisms_PlaceA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLocalUnitRepresentativesSplitPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler GlobalTheory.CMVal.Euler.Resid
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.Euler.Resid.le_exp_iff (x : WithZero (Multiplicative ℤ)) : x ≤ WithZero.exp (-((1 : ℕ) : ℤ)) ↔ x < 1 := by sorry
