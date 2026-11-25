-- Prove2me | Theorems.Thm_GlobalTheory_T_involutionIdempotentDecomposition_of_separable_charpoly
-- name    : GlobalTheory.T.involutionIdempotentDecomposition_of_separable_charpoly
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:33:58.419663+00:00
-- url     : https://prove2.me/theorems/42faa5c9-5b55-5b07-ad70-0962193db087
-- title:
--   T: involution Idempotent Decomposition of separable charpoly
-- statement:
--   The T construction uses the involution Idempotent Decomposition of separable charpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InvolutionIdempotentDecompositionOfSeparableCharStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InvolutionIdempotentDecompositionOfSeparableCharStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvolutionIdempotentDecompositionOfSeparableChar
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvolutionIdempotentDecompositionOfSeparableCharStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.involutionIdempotentDecomposition_of_separable_charpoly : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∃ (ι : Type) (_ : Fintype ι) (e : ι → B.A) (S : Finset ι), IsPre B e S := by sorry
