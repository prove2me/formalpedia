-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_Resid_val_iota_lt_iff
-- name    : GlobalTheory.CMVal.Euler.Resid.val_iota_lt_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:26.427965+00:00
-- url     : https://prove2.me/theorems/569e25ed-6ba1-42aa-8f9d-5ccdcccfddb1
-- title:
--   Resid: val iota lt iff
-- statement:
--   The Resid construction uses the val iota lt iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLocalUnitRepresentativesSplitPrime.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLocalUnitRepresentativesSplitPrime.lean#L22-L24

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

theorem GlobalTheory.CMVal.Euler.Resid.val_iota_lt_iff {P : HeightOneSpectrum (𝓞 E)} {q : HeightOneSpectrum (OF E)} (h : Over P q) (a : OF E) :
    Valued.v (iota a P) < 1 ↔ a ∈ q.asIdeal := by sorry
