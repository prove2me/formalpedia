-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_sel_mul
-- name    : GlobalTheory.CompanionTheory.Wedge.sel_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:03:52.624995+00:00
-- url     : https://prove2.me/theorems/e20bc852-b7b6-4eae-aeee-52e7b4e7653f
-- title:
--   Wedge: sel mul
-- statement:
--   The Wedge construction uses the sel mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L67-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L67-L70

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

theorem GlobalTheory.CompanionTheory.Wedge.sel_mul [DecidableEq ι] [Fintype ι] (s : κ → ι) (M : Matrix ι ι' K) :
    (1 : Matrix ι ι K).submatrix s id * M = M.submatrix s id := by sorry
