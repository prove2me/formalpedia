-- Prove2me | Theorems.Thm_GlobalTheory_weightedRelation_step
-- name    : GlobalTheory.weightedRelation_step
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:24:52.304114+00:00
-- url     : https://prove2.me/theorems/c2c34716-23aa-4725-89ca-fe9444b57037
-- title:
--   Global Theory: weighted Relation step
-- statement:
--   The Global Theory construction uses the weighted Relation step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffMemSpanOfWeightedHomogeneousRelationQuasiRe.lean#L49-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffMemSpanOfWeightedHomogeneousRelationQuasiRe.lean#L49-L111

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

theorem GlobalTheory.weightedRelation_step (z : Fin n → R) (w : Fin n → ℕ) (hw : ∀ i, 1 ≤ w i)
    (hz : IsQuasiRegularSeq R z) (D k : ℕ) (H : MvPolynomial (Fin n) R)
    (hH : ∀ β, H.coeff β ≠ 0 → k ≤ β.degree ∧ D ≤ Finsupp.weight w β)
    (h0 : MvPolynomial.eval z H = 0) :
    (∀ β : Fin n →₀ ℕ, β.degree = k → H.coeff β ∈ Ideal.span (Set.range z)) ∧
      ∃ H' : MvPolynomial (Fin n) R,
        (∀ β, H'.coeff β ≠ 0 → k + 1 ≤ β.degree ∧ D ≤ Finsupp.weight w β) ∧
        MvPolynomial.eval z H' = 0 ∧
        ∀ β : Fin n →₀ ℕ, Finsupp.weight w β = D → k + 1 ≤ β.degree → H'.coeff β = H.coeff β := by sorry
