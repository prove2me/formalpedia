-- Prove2me | Theorems.Thm_GlobalTheory_T_unitLemma_local_anyResidueChar_of_lieAlgebra
-- name    : GlobalTheory.T.unitLemma_local_anyResidueChar_of_lieAlgebra
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:59:41.356895+00:00
-- url     : https://prove2.me/theorems/71c296df-0cc0-512c-af31-b13107e423c6
-- title:
--   T: unit Lemma local any Residue Char of lie Algebra
-- statement:
--   The T construction uses the unit Lemma local any Residue Char of lie Algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitLemmaLocalAnyResidueCharOfLieAlgebraStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitLemmaLocalAnyResidueCharOfLieAlgebraStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitLemmaLocalAnyResidueCharOfLieAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitLemmaLocalAnyResidueCharOfLieAlgebraStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.unitLemma_local_anyResidueChar_of_lieAlgebra : UnitLemmaLie → ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) → InvAlg.Identity B₁ B₂ := by sorry
