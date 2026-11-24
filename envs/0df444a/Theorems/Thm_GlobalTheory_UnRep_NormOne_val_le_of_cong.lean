-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_NormOne_val_le_of_cong
-- name    : GlobalTheory.UnRep.NormOne.val_le_of_cong
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:24:20.372049+00:00
-- url     : https://prove2.me/theorems/0e8b3726-f92c-4882-adb0-0c7a9d87cf26
-- title:
--   Norm One: val le of cong
-- statement:
--   The Norm One construction uses the val le of cong property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/NormOneApproximationAtLevelPrimes.lean#L94-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/NormOneApproximationAtLevelPrimes.lean#L94-L129

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

theorem GlobalTheory.UnRep.NormOne.val_le_of_cong (P : HeightOneSpectrum (𝓞 E)) (N D D₁ D₂ k n : ℕ) (hD0 : 0 < D)
    (hM : D * n = D₁ * D₂) (h1 : D₁ ∣ N ^ k) (hN : (N : 𝓞 E) ∉ P.asIdeal) (hD : (D : 𝓞 E) ∈ P.asIdeal)
    (α β p b : 𝓞 E) (hab : p * D₂ + b = 1) :
    P.valuation E ((((p * D₂ * α + b : 𝓞 E) : E) / ((p * D₂ * β + b : 𝓞 E) : E) - 1) / D) ≤ 1 := by sorry
