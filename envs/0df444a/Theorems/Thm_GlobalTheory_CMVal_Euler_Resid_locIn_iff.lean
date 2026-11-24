-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_Resid_locIn_iff
-- name    : GlobalTheory.CMVal.Euler.Resid.locIn_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:05:17.385806+00:00
-- url     : https://prove2.me/theorems/58c22dd4-f88e-48fc-b9b5-99c030a3be67
-- title:
--   Resid: loc In iff
-- statement:
--   The Resid construction uses the loc In iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLocalUnitRepresentativesSplitPrime.lean#L44-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLocalUnitRepresentativesSplitPrime.lean#L44-L85

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

theorem GlobalTheory.CMVal.Euler.Resid.locIn_iff {q : HeightOneSpectrum (OF E)} {P P' : HeightOneSpectrum (𝓞 E)} (hP : Over P q) (hP' : Over P' q)
    (hne : P' ≠ P) (hall : ∀ R, Over R q → R = P ∨ R = P') (y : (Af E)ˣ) {a b t : OF E}
    (ha : Valued.v ((y : Af E) P' - iota a P') < 1) (hb : Valued.v ((y : Af E) P - iota b P) < 1)
    (ht : t ∉ q.asIdeal) (r : (P.adicCompletion E)ˣ) (hr : (r : P.adicCompletion E) = iota t P) :
    LocIn 1 q (((single P r)⁻¹ * y : (Af E)ˣ) : Af E) ↔ b - t * a ∈ q.asIdeal := by sorry
