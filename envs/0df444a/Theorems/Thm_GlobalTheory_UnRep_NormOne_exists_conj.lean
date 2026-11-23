-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_NormOne_exists_conj
-- name    : GlobalTheory.UnRep.NormOne.exists_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:34.967818+00:00
-- url     : https://prove2.me/theorems/c285dced-a1a6-48ab-b1bb-8e47e2f7cd27
-- title:
--   Norm One: exists conj
-- statement:
--   The Norm One construction uses the exists conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/NormOneApproximationAtLevelPrimes.lean#L134-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/NormOneApproximationAtLevelPrimes.lean#L134-L135

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
variable {F : Type} [Field F] [Algebra F E]
omit [NumberField E]

theorem GlobalTheory.UnRep.NormOne.exists_conj (c : E ≃ₐ[F] E) (x : 𝓞 E) : ∃ y : 𝓞 E, (y : E) = c x := by sorry
