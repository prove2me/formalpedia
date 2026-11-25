-- Prove2me | Theorems.Thm_GlobalTheory_coeff_mem_span_of_isWeightedHomogeneous_of_eval_eq_zero
-- name    : GlobalTheory.coeff_mem_span_of_isWeightedHomogeneous_of_eval_eq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:10:07.685471+00:00
-- url     : https://prove2.me/theorems/ccd43b90-ffe4-4f69-a7ef-661945304f96
-- title:
--   Global Theory: coeff mem span of is Weighted Homogeneous of eval eq zero
-- statement:
--   The Global Theory construction uses the coeff mem span of is Weighted Homogeneous of eval eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffMemSpanOfWeightedHomogeneousRelationQuasiRe.lean#L128-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffMemSpanOfWeightedHomogeneousRelationQuasiRe.lean#L128-L137

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffMemSpanOfWeightedHomogeneousRelationQuasiRe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory
open MvPolynomial
variable {R : Type} [CommRing R] {n : ℕ}

theorem GlobalTheory.coeff_mem_span_of_isWeightedHomogeneous_of_eval_eq_zero {R : Type} [CommRing R] {n : ℕ}
    (z : Fin n → R) (w : Fin n → ℕ) (hw : ∀ i, 1 ≤ w i) (hz : IsQuasiRegularSeq R z) (D : ℕ)
    (F : MvPolynomial (Fin n) R) (hF : F.IsWeightedHomogeneous w D)
    (h0 : MvPolynomial.eval z F = 0) (α : Fin n →₀ ℕ) :
    F.coeff α ∈ Ideal.span (Set.range z) := by sorry
