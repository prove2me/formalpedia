-- Prove2me | Theorems.Thm_GlobalTheory_weightedRelation_coeff_mem
-- name    : GlobalTheory.weightedRelation_coeff_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:24:09.822568+00:00
-- url     : https://prove2.me/theorems/f8c4fbe9-3e1c-446b-8e07-4e730d887528
-- title:
--   Global Theory: weighted Relation coeff mem
-- statement:
--   The Global Theory construction uses the weighted Relation coeff mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffMemSpanOfWeightedHomogeneousRelationQuasiRe.lean#L113-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffMemSpanOfWeightedHomogeneousRelationQuasiRe.lean#L113-L126

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

theorem GlobalTheory.weightedRelation_coeff_mem (z : Fin n → R) (w : Fin n → ℕ) (hw : ∀ i, 1 ≤ w i)
    (hz : IsQuasiRegularSeq R z) (D : ℕ) (j : ℕ) : ∀ (k : ℕ) (H : MvPolynomial (Fin n) R),
    (∀ β, H.coeff β ≠ 0 → k ≤ β.degree ∧ D ≤ Finsupp.weight w β) →
    MvPolynomial.eval z H = 0 → ∀ α : Fin n →₀ ℕ, α.degree = k + j →
    Finsupp.weight w α = D → H.coeff α ∈ Ideal.span (Set.range z) := by sorry
