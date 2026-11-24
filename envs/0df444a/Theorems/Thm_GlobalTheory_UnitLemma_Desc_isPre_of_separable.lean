-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Desc_isPre_of_separable
-- name    : GlobalTheory.UnitLemma.Desc.isPre_of_separable
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:27:55.277801+00:00
-- url     : https://prove2.me/theorems/78a60859-8603-4524-9527-c30d58ff79e0
-- title:
--   Desc: is Pre of separable
-- statement:
--   The Desc construction uses the is Pre of separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InvolutionIdempotentDecompositionOfSeparableChar.lean#L200-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InvolutionIdempotentDecompositionOfSeparableChar.lean#L200-L201

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsReducedOfSeparableMarkedCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvolutionIdempotentDecompositionOfSeparableChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open Classical

theorem GlobalTheory.UnitLemma.Desc.isPre_of_separable : ∀ (K : UQ) (B : InvAlg K), B.P.Separable →
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → B.A) (S : Finset ι), IsPre B e S := by sorry
