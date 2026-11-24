-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GramWedge_norm_entry_le_sz
-- name    : GlobalTheory.CompanionTheory.GramWedge.norm_entry_le_sz
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:43:36.593727+00:00
-- url     : https://prove2.me/theorems/8ca0762a-8174-4122-a470-b6ed3ec3d0a9
-- title:
--   Gram Wedge: norm entry le sz
-- statement:
--   The Gram Wedge construction uses the norm entry le sz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicativityInfinitePlaces.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicativityInfinitePlaces.lean#L18-L20

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

theorem GlobalTheory.CompanionTheory.GramWedge.norm_entry_le_sz {ι ι' : Type} [Fintype ι] [Fintype ι'] (g : Matrix ι' ι ℂ) (a : ι') (b : ι) :
    ‖g a b‖ ≤ sz g := by sorry
