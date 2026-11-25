-- Prove2me | Theorems.Thm_GlobalTheory_TensOp_sumMap_apply
-- name    : GlobalTheory.TensOp.sumMap_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:04:56.022238+00:00
-- url     : https://prove2.me/theorems/c594793b-dae1-41e6-a25b-c389e78b677d
-- title:
--   Tens Op: sum Map apply
-- statement:
--   The Tens Op construction uses the sum Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CompactCasimirLeTensorOperatorRaise.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CompactCasimirLeTensorOperatorRaise.lean#L34-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ReInnerLeOnImageOfIntertwiningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumNormAddSqLeOfBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CasKIsSymmetricAndFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CompactCasimirLeTensorOperatorRaise
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.TensOp

theorem GlobalTheory.TensOp.sumMap_apply {V N ι : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Fintype ι]
    [NormedAddCommGroup N] [InnerProductSpace ℂ N] (φ : ι → V →ₗ[ℂ] N) (x : PiLp 2 (fun _ : ι => V)) :
    sumMap φ x = ∑ j, φ j (x j) := by sorry
