-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GramWedge_sum_norm_mulVec_sq_le
-- name    : GlobalTheory.CompanionTheory.GramWedge.sum_norm_mulVec_sq_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:43:41.421816+00:00
-- url     : https://prove2.me/theorems/cec7fb0b-6ba1-408b-9096-c6bcfa33695b
-- title:
--   Gram Wedge: sum norm mul Vec sq le
-- statement:
--   The Gram Wedge construction uses the sum norm mul Vec sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicativityInfinitePlaces.lean#L22-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicativityInfinitePlaces.lean#L22-L43

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativityInfinitePlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.Rg.BcB.D1
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GramWedge

theorem GlobalTheory.CompanionTheory.GramWedge.sum_norm_mulVec_sq_le {ι ι' : Type} [Fintype ι] [Fintype ι'] (g : Matrix ι' ι ℂ) (v : ι → ℂ) :
    ∑ a, ‖(g *ᵥ v) a‖ ^ 2 ≤
      (Fintype.card ι * Fintype.card ι' : ℝ) * sz g ^ 2 * ∑ b, ‖v b‖ ^ 2 := by sorry
