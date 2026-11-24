-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_eq_mul_of_det_ne_zero
-- name    : GlobalTheory.CompanionTheory.Wedge.eq_mul_of_det_ne_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:21:14.209397+00:00
-- url     : https://prove2.me/theorems/9cb50d89-1110-411f-b41d-54ecda886bbe
-- title:
--   Wedge: eq mul of det ne zero
-- statement:
--   The Wedge construction uses the eq mul of det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PairingBoundFinitePlaces.lean#L17-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PairingBoundFinitePlaces.lean#L17-L33

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PairingBoundFinitePlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PositivityTheory.Rg.BcB.D1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Wedge

theorem GlobalTheory.CompanionTheory.Wedge.eq_mul_of_det_ne_zero {K ι κ : Type} [Field K] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι κ K) (s : κ → ι) (hd : (U.submatrix s id).det ≠ 0) :
    U = (Matrix.of fun i k => (U.submatrix s id).det⁻¹ *
      (U.submatrix (Function.update s k i) id).det) * U.submatrix s id := by sorry
