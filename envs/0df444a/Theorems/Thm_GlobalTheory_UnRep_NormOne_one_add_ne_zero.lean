-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_NormOne_one_add_ne_zero
-- name    : GlobalTheory.UnRep.NormOne.one_add_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:22:54.789393+00:00
-- url     : https://prove2.me/theorems/edc9e7e3-57dd-41e7-8cfc-ffe4e2d03a29
-- title:
--   Norm One: one add ne zero
-- statement:
--   The Norm One construction uses the one add ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/NormOneApproximationAtLevelPrimes.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/NormOneApproximationAtLevelPrimes.lean#L40-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationEqOneOfNormOneOfNotMoved
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsDenominatorPrimesPrescribed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneApproximationAtLevelPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.NormOne
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.UnRep.NormOne.one_add_ne_zero (N : ℕ) (hN : N ≠ 1) (z : 𝓞 E) : 1 + (N : 𝓞 E) * z ≠ 0 := by sorry
