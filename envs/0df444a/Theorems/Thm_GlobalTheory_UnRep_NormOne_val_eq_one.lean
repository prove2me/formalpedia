-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_NormOne_val_eq_one
-- name    : GlobalTheory.UnRep.NormOne.val_eq_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:22:56.519178+00:00
-- url     : https://prove2.me/theorems/8732e68e-f808-49f8-a2f1-2d9edb837cea
-- title:
--   Norm One: val eq one
-- statement:
--   The Norm One construction uses the val eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/NormOneApproximationAtLevelPrimes.lean#L73-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/NormOneApproximationAtLevelPrimes.lean#L73-L78

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

theorem GlobalTheory.UnRep.NormOne.val_eq_one (P : HeightOneSpectrum (𝓞 E)) (d : 𝓞 E) (hd : d ∉ P.asIdeal) :
    P.valuation E (d : E) = 1 := by sorry
