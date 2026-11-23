-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_gram_det_ne_zero_iff
-- name    : GlobalTheory.CompanionTheory.Wedge.gram_det_ne_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:50.242807+00:00
-- url     : https://prove2.me/theorems/08dcc5e1-c1ed-46ee-9602-129062d60e40
-- title:
--   Wedge: gram det ne zero iff
-- statement:
--   The Wedge construction uses the gram det ne zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundInfinitePlaces.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundInfinitePlaces.lean#L33-L38

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundInfinitePlaces
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Wedge
variable {ι κ κ' : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

theorem GlobalTheory.CompanionTheory.Wedge.gram_det_ne_zero_iff (A : Matrix ι κ ℂ) :
    (Aᴴ * A).det ≠ 0 ↔ LinearIndependent ℂ Aᵀ := by sorry
