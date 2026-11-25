-- Prove2me | Theorems.Thm_GlobalTheory_weightedRelation_coeff_mem_span
-- name    : GlobalTheory.weightedRelation_coeff_mem_span
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:24:35.057772+00:00
-- url     : https://prove2.me/theorems/98f9b545-3e81-45f8-8baa-fd7ba01f298d
-- title:
--   Global Theory: weighted Relation coeff mem span
-- statement:
--   The Global Theory construction uses the weighted Relation coeff mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffMemSpanOfWeightedHomogeneousRelationQuasiRe.lean#L139-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffMemSpanOfWeightedHomogeneousRelationQuasiRe.lean#L139-L145

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

theorem GlobalTheory.weightedRelation_coeff_mem_span : ∀ {R : Type} [CommRing R] {n : ℕ} (z : Fin n → R)
    (w : Fin n → ℕ), (∀ i, 1 ≤ w i) →
    IsQuasiRegularSeq R z → ∀ (D : ℕ) (F : MvPolynomial (Fin n) R),
    F.IsWeightedHomogeneous w D → MvPolynomial.eval z F = 0 →
    ∀ α : Fin n →₀ ℕ, F.coeff α ∈ Ideal.span (Set.range z) := by sorry
