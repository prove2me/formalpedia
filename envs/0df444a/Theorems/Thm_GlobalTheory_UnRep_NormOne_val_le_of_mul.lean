-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_NormOne_val_le_of_mul
-- name    : GlobalTheory.UnRep.NormOne.val_le_of_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:39.554645+00:00
-- url     : https://prove2.me/theorems/b63eae27-e2c2-4b0d-9ec9-a416843c27f9
-- title:
--   Norm One: val le of mul
-- statement:
--   The Norm One construction uses the val le of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/NormOneApproximationAtLevelPrimes.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/NormOneApproximationAtLevelPrimes.lean#L80-L83

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

theorem GlobalTheory.UnRep.NormOne.val_le_of_mul (P : HeightOneSpectrum (𝓞 E)) (x y : E) (d : 𝓞 E) (hd : d ∉ P.asIdeal)
    (h : x * d = y) (hy : P.valuation E y ≤ 1) : P.valuation E x ≤ 1 := by sorry
