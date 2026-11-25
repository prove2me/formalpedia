-- Prove2me | Theorems.Thm_GlobalTheory_T_coeff_mem_span_of_weightedHomogeneous_relation_quasiRegular
-- name    : GlobalTheory.T.coeff_mem_span_of_weightedHomogeneous_relation_quasiRegular
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:27:51.113394+00:00
-- url     : https://prove2.me/theorems/1a654667-205a-417a-8625-5189134217d7
-- title:
--   T: coeff mem span of weighted Homogeneous relation quasi Regular
-- statement:
--   The T construction uses the coeff mem span of weighted Homogeneous relation quasi Regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffMemSpanOfWeightedHomogeneousRelationQuasiReStatement.lean#L7-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffMemSpanOfWeightedHomogeneousRelationQuasiReStatement.lean#L7-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffMemSpanOfWeightedHomogeneousRelationQuasiRe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffMemSpanOfWeightedHomogeneousRelationQuasiReStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.coeff_mem_span_of_weightedHomogeneous_relation_quasiRegular : ∀ {R : Type} [CommRing R] {n : ℕ} (z : Fin n → R) (w : Fin n → ℕ), (∀ i, 1 ≤ w i) →
    IsQuasiRegularSeq R z → ∀ (D : ℕ) (F : MvPolynomial (Fin n) R),
    F.IsWeightedHomogeneous w D → MvPolynomial.eval z F = 0 →
    ∀ α : Fin n →₀ ℕ, F.coeff α ∈ Ideal.span (Set.range z) := by sorry
