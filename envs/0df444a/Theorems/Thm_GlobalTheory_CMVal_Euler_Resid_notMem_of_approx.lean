-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_Resid_notMem_of_approx
-- name    : GlobalTheory.CMVal.Euler.Resid.notMem_of_approx
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:06:46.581902+00:00
-- url     : https://prove2.me/theorems/d973d73e-970f-4626-9296-04e6126c0ac3
-- title:
--   Resid: not Mem of approx
-- statement:
--   The Resid construction uses the not Mem of approx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLocalUnitRepresentativesSplitPrime.lean#L87-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLocalUnitRepresentativesSplitPrime.lean#L87-L92

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

theorem GlobalTheory.CMVal.Euler.Resid.notMem_of_approx {q : HeightOneSpectrum (OF E)} {P : HeightOneSpectrum (𝓞 E)} (hP : Over P q)
    {x : P.adicCompletion E} (hx : Valued.v x = 1) {a : OF E} (ha : Valued.v (x - iota a P) < 1) : a ∉ q.asIdeal := by sorry
