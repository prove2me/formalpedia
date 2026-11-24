-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_Resid_exists_representatives
-- name    : GlobalTheory.CMVal.Euler.Resid.exists_representatives
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:05:11.431214+00:00
-- url     : https://prove2.me/theorems/90d9e343-2f97-441f-b76b-d37e308e6020
-- title:
--   Resid: exists representatives
-- statement:
--   The Resid construction uses the exists representatives property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLocalUnitRepresentativesSplitPrime.lean#L94-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLocalUnitRepresentativesSplitPrime.lean#L94-L148

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

theorem GlobalTheory.CMVal.Euler.Resid.exists_representatives : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (q : HeightOneSpectrum (OF E))
    (P : HeightOneSpectrum (𝓞 E)), Splits q → Over P q → ∃ R : Finset (P.adicCompletion E)ˣ,
      R.card + 1 = Ideal.absNorm q.asIdeal ∧ (∀ r ∈ R, Valued.v (r : P.adicCompletion E) = 1) ∧
      ∀ y : (Af E)ˣ, (∀ P', Over P' q → Valued.v ((y : Af E) P') = 1) →
        ∃! r, r ∈ R ∧ LocIn 1 q (((single P r)⁻¹ * y : (Af E)ˣ) : Af E) := by sorry
