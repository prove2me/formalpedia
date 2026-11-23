-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_nF_mul_le
-- name    : GlobalTheory.CompanionTheory.Wedge.nF_mul_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:47.646269+00:00
-- url     : https://prove2.me/theorems/e384ffbf-3742-4f10-92f4-af9ca71402e9
-- title:
--   Wedge: n F mul le
-- statement:
--   The Wedge construction uses the n F mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L60-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L60-L65

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundFinitePlaces
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Wedge
variable {K ι ι' κ κ' : Type} [NormedField K]

theorem GlobalTheory.CompanionTheory.Wedge.nF_mul_le (hM : MulF) [IsUltrametricDist K] [Fintype ι] [Fintype ι'] [Fintype κ]
    [DecidableEq κ] (g : Matrix ι' ι K) (A : Matrix ι κ K) (hg : ∀ i j, ‖g i j‖ ≤ 1) :
    nF (g * A) ≤ nF A := by sorry
