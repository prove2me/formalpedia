-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_NormOne_hilbert90_matrix_subalgebra_norm_one
-- name    : GlobalTheory.UnRep.NormOne.hilbert90_matrix_subalgebra_norm_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:22:45.37481+00:00
-- url     : https://prove2.me/theorems/a3cfa6c5-60dd-4d7b-982f-883af9e221d6
-- title:
--   Norm One: hilbert90 matrix subalgebra norm one
-- statement:
--   The Norm One construction uses the hilbert90 matrix subalgebra norm one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/NormOneApproximationAtLevelPrimes.lean#L137-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/NormOneApproximationAtLevelPrimes.lean#L137-L172

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

theorem GlobalTheory.UnRep.NormOne.hilbert90_matrix_subalgebra_norm_one (c : E ≃ₐ[F] E) (hc : ∀ x, c (c x) = x) (hc1 : c ≠ 1) (u : E) (hu : u * c u = 1) :
    ∃ α : 𝓞 E, α ≠ 0 ∧ u * c α = α := by sorry
