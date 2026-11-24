-- Prove2me | Theorems.Thm_GlobalTheory_exists_eval_eq_shift
-- name    : GlobalTheory.exists_eval_eq_shift
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:31:34.369371+00:00
-- url     : https://prove2.me/theorems/b4318f98-bd94-4a36-83c9-9965c95dac13
-- title:
--   Global Theory: exists eval eq shift
-- statement:
--   The Global Theory construction uses the exists eval eq shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffMemSpanOfWeightedHomogeneousRelationQuasiRe.lean#L20-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffMemSpanOfWeightedHomogeneousRelationQuasiRe.lean#L20-L47

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

theorem GlobalTheory.exists_eval_eq_shift (z : Fin n → R) (P : MvPolynomial (Fin n) R)
    (hP : ∀ β, P.coeff β ∈ Ideal.span (Set.range z)) :
    ∃ G : MvPolynomial (Fin n) R, MvPolynomial.eval z G = MvPolynomial.eval z P ∧
      ∀ γ, G.coeff γ ≠ 0 → ∃ β j, P.coeff β ≠ 0 ∧ γ = β + Finsupp.single j 1 := by sorry
